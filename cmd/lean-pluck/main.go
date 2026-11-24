// Command lean-pluck streams, records and plucks Lean 4 developments.
// Phase 1: graph extraction from an existing build, closure, closure
// reports, dependency queries, report diffs, and source cuts with a bin.
package main

import (
	"bufio"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strings"
	"time"

	"github.com/LaPingvino/lean-pluck/internal/cut"
	"github.com/LaPingvino/lean-pluck/internal/graph"
	"github.com/LaPingvino/lean-pluck/internal/project"
	"github.com/LaPingvino/lean-pluck/internal/report"
)

const usage = `lean-pluck: stream and pluck Lean 4 developments (phase-1 prototype)

  lean-pluck graph   -project DIR -toolchain DIR -store DIR -modules Mod[,Mod…]
        extract the declaration graph of the modules' import closure from an existing build
  lean-pluck closure -store DIR -targets A[,B…]           closure size and axioms
  lean-pluck why     -store DIR FROM TO                   does FROM depend on TO? print the path
  lean-pluck report  -project DIR -toolchain DIR -store DIR -targets A[,B…] [-local R] [-vendor Z] [-json F]
        closure report: axioms, hypotheses, packages, Mathlib areas, size
  lean-pluck diff    BEFORE.json AFTER.json               compare two report sets (exit 1 on new axioms/hypotheses)
  lean-pluck verify  -project DIR -toolchain DIR -store DIR -out DIR
        compile the plucked tree with stock lean (into DIR/build), compare statements and axioms
  lean-pluck relations -store DIR -out DIR               CSV relations (decl, uses, axiom, imports, extra_use)
  lean-pluck cut     -project DIR -store DIR -targets A[,B…] -pluck R[,R…] -out DIR [-bin-source]
        write the plucked source tree and the bin

Common flags: -extractor PATH (default: lean/.lake/build/bin/pluck-extract next to this repo)
`

func main() {
	if len(os.Args) < 2 {
		fmt.Fprint(os.Stderr, usage)
		os.Exit(2)
	}
	cmd, args := os.Args[1], os.Args[2:]
	fs := flag.NewFlagSet(cmd, flag.ExitOnError)
	projDir := fs.String("project", ".", "Lake workspace")
	toolchain := fs.String("toolchain", "", "toolchain directory matching the oleans (contains bin/lean)")
	store := fs.String("store", "store", "store directory (graph shards)")
	mods := fs.String("modules", "", "comma-separated root modules")
	targets := fs.String("targets", "", "comma-separated target constants")
	local := fs.String("local", "", "comma-separated module roots that are the project itself")
	vendor := fs.String("vendor", "", "comma-separated module roots that are vendored")
	jsonOut := fs.String("json", "", "write reports as JSON to this file")
	pluck := fs.String("pluck", "", "comma-separated module roots whose sources are cut")
	out := fs.String("out", "out", "output directory")
	binSource := fs.Bool("bin-source", false, "also keep the removed source text in bin/src")
	extractor := fs.String("extractor", defaultExtractor(), "pluck-extract binary")
	fs.Parse(args)

	var err error
	switch cmd {
	case "graph":
		err = cmdGraph(*projDir, *toolchain, *store, *extractor, split(*mods))
	case "closure":
		err = cmdClosure(*store, split(*targets))
	case "why":
		if fs.NArg() != 2 {
			err = fmt.Errorf("why FROM TO")
			break
		}
		err = cmdWhy(*store, fs.Arg(0), fs.Arg(1))
	case "report":
		err = cmdReport(*projDir, *toolchain, *store, *extractor, split(*targets), split(*local), split(*vendor), *jsonOut)
	case "diff":
		if fs.NArg() != 2 {
			err = fmt.Errorf("diff BEFORE.json AFTER.json")
			break
		}
		err = cmdDiff(fs.Arg(0), fs.Arg(1))
	case "verify":
		err = cmdVerify(*projDir, *toolchain, *store, *extractor, *out)
	case "relations":
		err = cmdRelations(*store, *out)
	case "cut":
		err = cmdCut(*projDir, *toolchain, *store, split(*targets), split(*pluck), *out, *binSource)
	default:
		fmt.Fprint(os.Stderr, usage)
		os.Exit(2)
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, "lean-pluck:", err)
		os.Exit(1)
	}
}

func defaultExtractor() string {
	exe, err := os.Executable()
	if err != nil {
		return "pluck-extract"
	}
	for d := filepath.Dir(exe); d != "/"; d = filepath.Dir(d) {
		p := filepath.Join(d, "lean", ".lake", "build", "bin", "pluck-extract")
		if _, err := os.Stat(p); err == nil {
			return p
		}
	}
	return "pluck-extract"
}

func split(s string) []string {
	var out []string
	for _, x := range strings.Split(s, ",") {
		if x = strings.TrimSpace(x); x != "" {
			out = append(out, x)
		}
	}
	return out
}

func set(xs []string) map[string]bool {
	m := map[string]bool{}
	for _, x := range xs {
		m[x] = true
	}
	return m
}

func cmdGraph(projDir, toolchain, store, extractor string, roots []string) error {
	if toolchain == "" {
		return fmt.Errorf("-toolchain is required")
	}
	p, err := project.Load(projDir, toolchain)
	if err != nil {
		return err
	}
	order, _, err := p.ImportClosure(roots)
	if err != nil {
		return err
	}
	var jobs []graph.Job
	for _, m := range order {
		o, _, ok := p.OLean(m)
		if !ok {
			return fmt.Errorf("no .olean for %s (build the project first)", m)
		}
		jobs = append(jobs, graph.Job{Mod: m, OLean: o})
	}
	t0 := time.Now()
	fmt.Fprintf(os.Stderr, "extracting %d modules (import closure of %s)\n", len(jobs), strings.Join(roots, ", "))
	n, err := graph.Extract(extractor, store, nil, jobs, os.Stderr)
	fmt.Fprintf(os.Stderr, "extracted %d new shards in %s\n", n, time.Since(t0).Round(time.Second))
	return err
}

func cmdClosure(store string, targets []string) error {
	g, err := graph.LoadStore(store)
	if err != nil {
		return err
	}
	c := g.Close(targets)
	fmt.Printf("closure of %s: %d constants\naxioms: %s\n", strings.Join(targets, ", "), len(c.Set), strings.Join(g.Axioms(c), ", "))
	if len(c.Missing) > 0 {
		fmt.Printf("missing from graph: %d (e.g. %s)\n", len(c.Missing), c.Missing[0])
	}
	return nil
}

func cmdWhy(store, from, to string) error {
	g, err := graph.LoadStore(store)
	if err != nil {
		return err
	}
	if g.Decls[from] == nil {
		return fmt.Errorf("%s is not in the graph", from)
	}
	p := g.Path(from, to)
	if p == nil {
		fmt.Printf("no: %s does not depend on %s\n", from, to)
		os.Exit(3)
	}
	fmt.Printf("yes: %s depends on %s (path of %d steps)\n", from, to, len(p)-1)
	for i, n := range p {
		mod := ""
		if d := g.Decls[n]; d != nil {
			mod = d.Mod
		}
		if i == 0 {
			fmt.Printf("  %s  [%s]\n", n, mod)
			continue
		}
		fmt.Printf("    → %s  [%s]  (in %s of %s)\n", n, mod, g.EdgeWhere(p[i-1], n), p[i-1])
	}
	return nil
}

func cmdRelations(store, out string) error {
	g, err := graph.LoadStore(store)
	if err != nil {
		return err
	}
	return g.WriteRelations(out)
}

func stmtOf(p *project.Project, g *graph.Graph, extractor, target string) (*report.Stmt, error) {
	d := g.Decls[target]
	if d == nil {
		return nil, fmt.Errorf("%s is not in the graph", target)
	}
	o, _, ok := p.OLean(d.Mod)
	if !ok {
		return nil, fmt.Errorf("no olean for %s", d.Mod)
	}
	out, err := exec.Command(extractor, "stmt", target, o).Output()
	if err != nil {
		return nil, fmt.Errorf("stmt %s: %w", target, err)
	}
	var st report.Stmt
	if err := json.Unmarshal(out, &st); err != nil {
		return nil, err
	}
	return &st, nil
}

func cmdReport(projDir, toolchain, store, extractor string, targets, local, vendor []string, jsonOut string) error {
	p, err := project.Load(projDir, toolchain)
	if err != nil {
		return err
	}
	g, err := graph.LoadStore(store)
	if err != nil {
		return err
	}
	opt := report.Options{LocalRoots: set(local), VendorRoots: set(vendor)}
	var rs []*report.Report
	w := bufio.NewWriter(os.Stdout)
	defer w.Flush()
	fmt.Fprintf(w, "# Closure report\n\n")
	for _, t := range targets {
		st, err := stmtOf(p, g, extractor, t)
		if err != nil {
			return err
		}
		r := report.Build(g, st, opt)
		rs = append(rs, r)
		report.Markdown(w, r)
	}
	if jsonOut != "" {
		f, err := os.Create(jsonOut)
		if err != nil {
			return err
		}
		defer f.Close()
		return report.WriteJSON(f, rs)
	}
	return nil
}

func cmdDiff(a, b string) error {
	load := func(f string) ([]*report.Report, error) {
		data, err := os.ReadFile(f)
		if err != nil {
			return nil, err
		}
		var rs []*report.Report
		return rs, json.Unmarshal(data, &rs)
	}
	before, err := load(a)
	if err != nil {
		return err
	}
	after, err := load(b)
	if err != nil {
		return err
	}
	if report.Diff(os.Stdout, before, after) {
		fmt.Println("\nGATE: a non-standard axiom or a new hypothesis entered.")
		os.Exit(1)
	}
	return nil
}

func cmdCut(projDir, toolchain, store string, targets, pluck []string, out string, binSource bool) error {
	p, err := project.Load(projDir, toolchain)
	if err != nil {
		return err
	}
	g, err := graph.LoadStore(store)
	if err != nil {
		return err
	}
	res, err := cut.Run(g, p, targets, cut.Options{PluckRoots: set(pluck), Out: out, BinSource: binSource}, os.Stderr)
	if err != nil {
		return err
	}
	sort.Strings(res.EmptiedFiles)
	fmt.Printf("plucked %d files: %d commands kept, %d binned; %d → %d lines. Output in %s\n",
		len(res.Modules), res.KeptCmds, res.BinnedCmds, res.LinesBefore, res.LinesAfter, out)
	return nil
}

func cmdVerify(projDir, toolchain, store, extractor, out string) error {
	if toolchain == "" {
		return fmt.Errorf("-toolchain is required")
	}
	p, err := project.Load(projDir, toolchain)
	if err != nil {
		return err
	}
	g, err := graph.LoadStore(store)
	if err != nil {
		return err
	}
	if err := cut.Verify(g, p, out, extractor, nil, os.Stderr); err != nil {
		return err
	}
	fmt.Println("verified: the plucked tree compiles; target statements and axioms unchanged")
	return nil
}
