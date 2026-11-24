// Package cut turns a closure into a plucked source tree plus a bin of
// everything removed. Phase 1 plucks only the project's own packages; their
// dependencies (Mathlib, vendored packages) stay as they are.
package cut

import (
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"unicode/utf8"

	"github.com/LaPingvino/lean-pluck/internal/graph"
	"github.com/LaPingvino/lean-pluck/internal/project"
)

// Command is one source span owning one or more constants.
type Command struct {
	Mod        string
	Start, End pos // inclusive start, exclusive end
	Decls      []string
	Kept       bool
}

type pos struct{ Line, Col int }

func (a pos) less(b pos) bool { return a.Line < b.Line || (a.Line == b.Line && a.Col < b.Col) }

// BinEntry is one record of bin/index.jsonl.
type BinEntry struct {
	Decls     []string `json:"decls"`
	Kind      string   `json:"kind"`
	Module    string   `json:"module"`
	File      string   `json:"file"`
	Lines     [2]int   `json:"lines"`
	Bytes     int      `json:"bytes"`
	TermSize  int      `json:"term_size"`
	Statement string   `json:"statement"`
	Reason    string   `json:"reason"`
	UsedBy    []string `json:"used_by,omitempty"` // other binned constants that use it
}

// Result summarises a cut.
type Result struct {
	Targets      []string   `json:"targets"`
	Modules      []string   `json:"modules"`
	KeptCmds     int        `json:"kept_commands"`
	BinnedCmds   int        `json:"binned_commands"`
	LinesBefore  int        `json:"lines_before"`
	LinesAfter   int        `json:"lines_after"`
	EmptiedFiles []string   `json:"emptied_files"`
	Bin          []BinEntry `json:"-"`
}

// Options control a cut.
type Options struct {
	PluckRoots map[string]bool // module roots whose sources are cut (e.g. Riemann)
	Out        string
	BinSource  bool
}

// Run cuts the project's own modules in the import closure of the targets.
func Run(g *graph.Graph, p *project.Project, targets []string, opt Options, log io.Writer) (*Result, error) {
	cl := g.Close(targets)
	var tmods []string
	for _, t := range targets {
		d := g.Decls[t]
		if d == nil {
			return nil, fmt.Errorf("target %s not in graph", t)
		}
		tmods = append(tmods, d.Mod)
	}
	order, _, err := p.ImportClosure(tmods)
	if err != nil {
		return nil, err
	}
	res := &Result{Targets: targets}
	srcDir := filepath.Join(opt.Out, "src")
	binDir := filepath.Join(opt.Out, "bin")
	for _, d := range []string{srcDir, binDir} {
		if err := os.MkdirAll(d, 0o755); err != nil {
			return nil, err
		}
	}
	// reverse uses among constants, for the bin's "used_by"
	rev := map[string][]string{}
	for n := range g.Decls {
		for _, m := range g.Deps(n) {
			rev[m] = append(rev[m], n)
		}
	}
	var binSrc = map[string]*strings.Builder{}
	for _, mod := range order {
		if !opt.PluckRoots[graph.Root(mod)] {
			continue
		}
		res.Modules = append(res.Modules, mod)
		src, ok := p.Source(mod)
		if !ok {
			return nil, fmt.Errorf("no source for %s", mod)
		}
		text, err := os.ReadFile(src)
		if err != nil {
			return nil, err
		}
		rel, _ := filepath.Rel(p.Root, src)
		cmds := commands(g, mod)
		kept := 0
		for _, c := range cmds {
			for _, n := range c.Decls {
				if cl.Set[n] || isMeta(g.Decls[n]) {
					c.Kept = true
					break
				}
			}
			if c.Kept {
				kept++
			}
		}
		lines := strings.Split(string(text), "\n")
		res.LinesBefore += len(lines)
		var out strings.Builder
		cursor := pos{1, 0}
		emit := func(from, to pos, w *strings.Builder) { w.WriteString(slice(lines, from, to)) }
		for _, c := range cmds {
			if c.Kept {
				res.KeptCmds++
				continue
			}
			res.BinnedCmds++
			emit(cursor, c.Start, &out)
			body := slice(lines, c.Start, c.End)
			e := BinEntry{Decls: c.Decls, Module: mod, File: rel, Lines: [2]int{c.Start.Line, c.End.Line},
				Bytes: len(body), Statement: statement(body), Reason: "unreachable"}
			if d := g.Decls[c.Decls[0]]; d != nil {
				e.Kind = d.Kind
			}
			usedBy := map[string]bool{}
			for _, n := range c.Decls {
				if d := g.Decls[n]; d != nil {
					e.TermSize += d.TSize + d.VSize
				}
				for _, u := range rev[n] {
					if !contains(c.Decls, u) && g.Decls[u] != nil && opt.PluckRoots[graph.Root(g.Decls[u].Mod)] {
						usedBy[u] = true
					}
				}
			}
			for u := range usedBy {
				e.UsedBy = append(e.UsedBy, u)
			}
			sort.Strings(e.UsedBy)
			if len(e.UsedBy) == 0 {
				e.Reason = "unreachable; used by nothing in the project"
			}
			res.Bin = append(res.Bin, e)
			if opt.BinSource {
				b := binSrc[rel]
				if b == nil {
					b = &strings.Builder{}
					binSrc[rel] = b
				}
				fmt.Fprintf(b, "-- [bin] %s lines %d–%d\n%s\n\n", rel, c.Start.Line, c.End.Line, body)
			}
			cursor = c.End
		}
		emit(cursor, pos{len(lines) + 1, 0}, &out)
		cleaned := squeezeBlank(out.String())
		if kept == 0 {
			res.EmptiedFiles = append(res.EmptiedFiles, mod)
		}
		res.LinesAfter += strings.Count(cleaned, "\n") + 1
		header := fmt.Sprintf("-- lean-pluck: plucked from %s for %s; %d of %d declarations kept, the rest in bin/.\n",
			rel, strings.Join(targets, ", "), kept, len(cmds))
		dst := filepath.Join(srcDir, rel)
		if err := os.MkdirAll(filepath.Dir(dst), 0o755); err != nil {
			return nil, err
		}
		if err := os.WriteFile(dst, []byte(insertAfterHeader(cleaned, header)), 0o644); err != nil {
			return nil, err
		}
	}
	// bin index, sources and report
	f, err := os.Create(filepath.Join(binDir, "index.jsonl"))
	if err != nil {
		return nil, err
	}
	enc := json.NewEncoder(f)
	for _, e := range res.Bin {
		enc.Encode(e)
	}
	f.Close()
	for rel, b := range binSrc {
		dst := filepath.Join(binDir, "src", rel)
		os.MkdirAll(filepath.Dir(dst), 0o755)
		if err := os.WriteFile(dst, []byte(b.String()), 0o644); err != nil {
			return nil, err
		}
	}
	writeBinReport(filepath.Join(binDir, "REPORT.md"), res)
	sum, _ := json.MarshalIndent(res, "", " ")
	return res, os.WriteFile(filepath.Join(opt.Out, "PLUCK.json"), sum, 0o644)
}

// commands groups a module's constants into source commands: constants with
// a declaration range own the span; nested spans (structure fields) and
// constants without a range (aux: match_, proof_, eq_, instances' helpers)
// join their enclosing or name-prefix command.
func commands(g *graph.Graph, mod string) []*Command {
	m := g.Modules[mod]
	if m == nil {
		return nil
	}
	var cmds []*Command
	var noRange []string
	for _, n := range m.Decls {
		d := g.Decls[n]
		if len(d.Rng) < 4 {
			noRange = append(noRange, n)
			continue
		}
		cmds = append(cmds, &Command{Mod: mod, Start: pos{d.Rng[0], d.Rng[1]}, End: pos{d.Rng[2], d.Rng[3]}, Decls: []string{n}})
	}
	sort.Slice(cmds, func(i, j int) bool {
		if cmds[i].Start != cmds[j].Start {
			return cmds[i].Start.less(cmds[j].Start)
		}
		return cmds[j].End.less(cmds[i].End) // outer first
	})
	// merge contained or identical spans into the outer command
	var merged []*Command
	for _, c := range cmds {
		if k := len(merged); k > 0 && c.Start.less(merged[k-1].End) && !merged[k-1].End.less(c.End) {
			merged[k-1].Decls = append(merged[k-1].Decls, c.Decls...)
			continue
		}
		merged = append(merged, c)
	}
	owner := map[string]*Command{}
	for _, c := range merged {
		for _, n := range c.Decls {
			owner[n] = c
			owner[stripPrivate(n)] = c
		}
	}
	for _, n := range noRange {
		for p := prefix(stripPrivate(n)); p != ""; p = prefix(p) {
			if c := owner[p]; c != nil {
				c.Decls = append(c.Decls, n)
				break
			}
		}
		// constants with no ranged ancestor (rare) are never cut: they stay
		// wherever their generating command is, which we cannot locate.
	}
	return merged
}

// metaTypes mark constants that change how later commands parse or
// elaborate (syntax, macros, elaborators, delaborators, simprocs). Their uses
// leave no trace in terms, so commands defining them are never cut
// (DESIGN §5.3, rule 3, at command granularity).
var metaTypes = map[string]bool{
	"Lean.ParserDescr": true, "Lean.TrailingParserDescr": true, "Lean.Parser.Parser": true,
	"Lean.Parser.TrailingParser": true, "Lean.Macro": true, "Lean.Elab.Term.TermElab": true,
	"Lean.Elab.Tactic.Tactic": true, "Lean.Elab.Command.CommandElab": true,
	"Lean.PrettyPrinter.Delaborator.Delab": true, "Lean.PrettyPrinter.Unexpander": true,
	"Lean.Meta.Simp.Simproc": true, "Lean.Meta.Simp.DSimproc": true,
	"Lean.Meta.Simp.SimprocDeclExtension": true, "Lean.SyntaxNodeKind": true,
}

func isMeta(d *graph.Decl) bool {
	if d == nil {
		return false
	}
	for _, t := range d.Ty {
		if metaTypes[t] {
			return true
		}
	}
	return false
}

// stripPrivate turns `_private.Mod.Path.0.Foo.bar` into `Foo.bar`.
func stripPrivate(n string) string {
	if !strings.HasPrefix(n, "_private.") {
		return n
	}
	if i := strings.Index(n, ".0."); i >= 0 {
		return n[i+3:]
	}
	return n
}

func prefix(n string) string {
	if i := strings.LastIndexByte(n, '.'); i > 0 {
		return n[:i]
	}
	return ""
}

// slice returns the text from a to b (lines 1-based, columns in code points).
func slice(lines []string, a, b pos) string {
	var sb strings.Builder
	for l := a.Line; l <= b.Line && l <= len(lines); l++ {
		s := lines[l-1]
		from, to := 0, len(s)
		if l == a.Line {
			from = byteOff(s, a.Col)
		}
		if l == b.Line {
			to = byteOff(s, b.Col)
		}
		if from < to {
			sb.WriteString(s[from:to])
		}
		if l < b.Line {
			sb.WriteByte('\n')
		}
	}
	return sb.String()
}

func byteOff(s string, col int) int {
	i := 0
	for c := 0; c < col && i < len(s); c++ {
		_, w := utf8.DecodeRuneInString(s[i:])
		i += w
	}
	return i
}

func statement(body string) string {
	s := body
	if i := strings.Index(s, ":="); i >= 0 {
		s = s[:i]
	}
	if i := strings.Index(s, " where"); i >= 0 {
		s = s[:i]
	}
	// drop the doc comment, keep the declaration head
	if i := strings.Index(s, "-/"); i >= 0 && strings.HasPrefix(strings.TrimSpace(s), "/-") {
		s = s[i+2:]
	}
	s = strings.Join(strings.Fields(s), " ")
	if len(s) > 400 {
		s = s[:400] + " …"
	}
	return s
}

func squeezeBlank(s string) string {
	for strings.Contains(s, "\n\n\n\n") {
		s = strings.ReplaceAll(s, "\n\n\n\n", "\n\n\n")
	}
	return s
}

func insertAfterHeader(text, line string) string { return line + text }

func contains(xs []string, x string) bool {
	for _, y := range xs {
		if y == x {
			return true
		}
	}
	return false
}

func writeBinReport(path string, r *Result) {
	var b strings.Builder
	fmt.Fprintf(&b, "# The bin\n\nTargets: %s\n\n", strings.Join(r.Targets, ", "))
	fmt.Fprintf(&b, "%d commands kept, %d binned; %d → %d source lines across %d files.\n\n",
		r.KeptCmds, r.BinnedCmds, r.LinesBefore, r.LinesAfter, len(r.Modules))
	if len(r.EmptiedFiles) > 0 {
		fmt.Fprintf(&b, "Files with no declaration left (kept only for their imports): %s\n\n", strings.Join(r.EmptiedFiles, ", "))
	}
	orphans := 0
	for _, e := range r.Bin {
		if len(e.UsedBy) == 0 {
			orphans++
		}
	}
	fmt.Fprintf(&b, "%d binned commands are used by nothing else in the project at all.\n\n", orphans)
	bySize := append([]BinEntry(nil), r.Bin...)
	sort.Slice(bySize, func(i, j int) bool { return bySize[i].TermSize > bySize[j].TermSize })
	fmt.Fprintf(&b, "## Largest binned declarations (by term size)\n\n| declaration | file | lines | term size |\n|---|---|---|---|\n")
	for i, e := range bySize {
		if i == 25 {
			break
		}
		fmt.Fprintf(&b, "| `%s` | %s | %d–%d | %d |\n", e.Decls[0], e.File, e.Lines[0], e.Lines[1], e.TermSize)
	}
	byName := append([]BinEntry(nil), r.Bin...)
	sort.Slice(byName, func(i, j int) bool { return len(byName[i].Decls[0]) > len(byName[j].Decls[0]) })
	fmt.Fprintf(&b, "\n## Longest names in the bin\n\n")
	for i, e := range byName {
		if i == 5 {
			break
		}
		fmt.Fprintf(&b, "* `%s`\n", e.Decls[0])
	}
	os.WriteFile(path, []byte(b.String()), 0o644)
}
