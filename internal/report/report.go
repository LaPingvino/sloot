// Package report builds the per-theorem closure report ("what does this
// theorem rest on?") and diffs two sets of reports.
package report

import (
	"encoding/json"
	"fmt"
	"io"
	"sort"
	"strings"

	"github.com/LaPingvino/lean-pluck/internal/graph"
)

// StandardAxioms are the three axioms Lean's own library uses.
var StandardAxioms = map[string]bool{"propext": true, "Classical.choice": true, "Quot.sound": true}

// Binder is one ∀-binder of a statement, as printed by `pluck-extract stmt`.
type Binder struct {
	Name string   `json:"name"`
	BI   string   `json:"bi"`
	Head *string  `json:"head"`
	Uses []string `json:"uses"`
	Dbg  string   `json:"dbg"`
}

// Stmt is the statement record of one target.
type Stmt struct {
	Name    string   `json:"n"`
	Kind    string   `json:"k"`
	Binders []Binder `json:"binders"`
	Concl   struct {
		Head *string  `json:"head"`
		Uses []string `json:"uses"`
		Dbg  string   `json:"dbg"`
	} `json:"concl"`
}

// Hyp is a classified binder.
type Hyp struct {
	Name string `json:"name"`
	Role string `json:"role"` // hypothesis | parameter | instance | unknown
	Head string `json:"head,omitempty"`
	// Local is true when the hypothesis' head is defined in the project
	// itself (a project-specific assumption such as a `StarBound`).
	Local bool   `json:"local,omitempty"`
	Text  string `json:"text"`
}

// Report is the closure report of one theorem.
type Report struct {
	Target       string         `json:"target"`
	Kind         string         `json:"kind"`
	Module       string         `json:"module"`
	Line         int            `json:"line,omitempty"`
	Axioms       []string       `json:"axioms"`
	NonStandard  []string       `json:"nonstandard_axioms"`
	Hypotheses   []Hyp          `json:"hypotheses"`
	Parameters   []Hyp          `json:"parameters"`
	Conclusion   string         `json:"conclusion_head,omitempty"`
	Constants    int            `json:"closure_constants"`
	TermSize     int            `json:"closure_term_size"`
	ByPackage    map[string]int `json:"by_package"`
	Areas        map[string]int `json:"mathlib_areas"`
	Local        []string       `json:"local"`    // closure constants from the project's own packages
	Vendored     []string       `json:"vendored"` // closure constants from vendored packages
	LocalModules []string       `json:"local_modules"`
	Missing      []string       `json:"missing,omitempty"`
}

// Options say which module roots are "the project" and which are vendored.
type Options struct {
	LocalRoots  map[string]bool // e.g. Riemann
	VendorRoots map[string]bool // e.g. Zeta23
}

// Build computes the report for one target.
func Build(g *graph.Graph, st *Stmt, opt Options) *Report {
	c := g.Close([]string{st.Name})
	r := &Report{Target: st.Name, Kind: st.Kind, ByPackage: map[string]int{}, Areas: map[string]int{},
		Missing: c.Missing}
	if d := g.Decls[st.Name]; d != nil {
		r.Module = d.Mod
		if len(d.Rng) > 0 {
			r.Line = d.Rng[0]
		}
	}
	r.Axioms = g.Axioms(c)
	for _, a := range r.Axioms {
		if !StandardAxioms[a] {
			r.NonStandard = append(r.NonStandard, a)
		}
	}
	mods := map[string]bool{}
	for n := range c.Set {
		d := g.Decls[n]
		if d == nil {
			continue
		}
		r.Constants++
		r.TermSize += d.TSize + d.VSize
		root := graph.Root(d.Mod)
		r.ByPackage[root]++
		if root == "Mathlib" {
			r.Areas[graph.Area(d.Mod)]++
		}
		if opt.LocalRoots[root] {
			r.Local = append(r.Local, n)
			mods[d.Mod] = true
		}
		if opt.VendorRoots[root] {
			r.Vendored = append(r.Vendored, n)
			mods[d.Mod] = true
		}
	}
	for m := range mods {
		r.LocalModules = append(r.LocalModules, m)
	}
	sort.Strings(r.Local)
	sort.Strings(r.Vendored)
	sort.Strings(r.LocalModules)
	for _, b := range st.Binders {
		h := Hyp{Name: b.Name, Text: b.Dbg}
		if b.Head != nil {
			h.Head = *b.Head
			if d := g.Decls[h.Head]; d != nil {
				h.Local = opt.LocalRoots[graph.Root(d.Mod)] || opt.VendorRoots[graph.Root(d.Mod)]
			}
		}
		switch {
		case b.BI == "Lean.BinderInfo.instImplicit":
			h.Role = "instance"
		case b.Head == nil:
			h.Role = "unknown"
		case g.Decls[h.Head] != nil && g.Decls[h.Head].RetPrp:
			h.Role = "hypothesis"
		default:
			h.Role = "parameter"
		}
		if h.Role == "hypothesis" || h.Role == "unknown" {
			r.Hypotheses = append(r.Hypotheses, h)
		} else {
			r.Parameters = append(r.Parameters, h)
		}
	}
	if st.Concl.Head != nil {
		r.Conclusion = *st.Concl.Head
	}
	return r
}

// Markdown renders a report for humans.
func Markdown(w io.Writer, r *Report) {
	fmt.Fprintf(w, "## `%s`\n\n", r.Target)
	fmt.Fprintf(w, "%s in `%s`", r.Kind, r.Module)
	if r.Line > 0 {
		fmt.Fprintf(w, ", line %d", r.Line)
	}
	fmt.Fprintf(w, ".\n\n")
	if len(r.NonStandard) == 0 {
		fmt.Fprintf(w, "**Axioms:** standard only (%s).\n\n", strings.Join(r.Axioms, ", "))
	} else {
		fmt.Fprintf(w, "**Axioms:** %s. **Non-standard: %s.**\n\n", strings.Join(r.Axioms, ", "),
			strings.Join(r.NonStandard, ", "))
	}
	if len(r.Hypotheses) == 0 {
		fmt.Fprintf(w, "**Hypotheses:** none: the statement is unconditional.\n\n")
	} else {
		fmt.Fprintf(w, "**Hypotheses** (propositions the statement takes as arguments):\n\n")
		for _, h := range r.Hypotheses {
			loc := ""
			if h.Local {
				loc = " (project-defined)"
			}
			fmt.Fprintf(w, "* `%s` : `%s`%s, %s\n", h.Name, h.Head, loc, h.Role)
		}
		fmt.Fprintln(w)
	}
	if len(r.Parameters) > 0 {
		var ps []string
		for _, p := range r.Parameters {
			ps = append(ps, fmt.Sprintf("`%s`", p.Name))
		}
		fmt.Fprintf(w, "**Parameters:** %s.\n\n", strings.Join(ps, ", "))
	}
	fmt.Fprintf(w, "**Size:** %d constants in the closure; term size %d.\n\n", r.Constants, r.TermSize)
	fmt.Fprintf(w, "| package | constants |\n|---|---|\n")
	for _, kv := range sortedDesc(r.ByPackage) {
		fmt.Fprintf(w, "| %s | %d |\n", kv.k, kv.v)
	}
	fmt.Fprintln(w)
	fmt.Fprintf(w, "**Project and vendored modules used:** %d (%s).\n\n", len(r.LocalModules),
		strings.Join(r.LocalModules, ", "))
	fmt.Fprintf(w, "**Project constants:** %d. **Vendored constants:** %d.\n\n", len(r.Local), len(r.Vendored))
	if len(r.Areas) > 0 {
		fmt.Fprintf(w, "**Mathlib areas** (constants):")
		for i, kv := range sortedDesc(r.Areas) {
			if i == 12 {
				fmt.Fprintf(w, " …")
				break
			}
			fmt.Fprintf(w, " %s %d;", strings.TrimPrefix(kv.k, "Mathlib."), kv.v)
		}
		fmt.Fprintf(w, "\n\n")
	}
	if len(r.Missing) > 0 {
		fmt.Fprintf(w, "_Referenced but not in the graph:_ %d (e.g. `%s`).\n\n", len(r.Missing), r.Missing[0])
	}
}

type kv struct {
	k string
	v int
}

func sortedDesc(m map[string]int) []kv {
	var out []kv
	for k, v := range m {
		out = append(out, kv{k, v})
	}
	sort.Slice(out, func(i, j int) bool {
		if out[i].v != out[j].v {
			return out[i].v > out[j].v
		}
		return out[i].k < out[j].k
	})
	return out
}

// WriteJSON writes reports as indented JSON.
func WriteJSON(w io.Writer, rs []*Report) error {
	e := json.NewEncoder(w)
	e.SetIndent("", " ")
	return e.Encode(rs)
}

// Diff compares two report sets (for example, two commits). It returns a
// Markdown summary and whether anything a session gate must stop on changed:
// a new non-standard axiom or a new hypothesis.
func Diff(w io.Writer, before, after []*Report) (gate bool) {
	idx := map[string]*Report{}
	for _, r := range before {
		idx[r.Target] = r
	}
	seen := map[string]bool{}
	for _, a := range after {
		seen[a.Target] = true
		b := idx[a.Target]
		if b == nil {
			fmt.Fprintf(w, "* `%s`: **new** (%d constants, axioms %s)\n", a.Target, a.Constants, strings.Join(a.Axioms, ", "))
			if len(a.NonStandard) > 0 {
				gate = true
			}
			continue
		}
		addAx, delAx := setDiff(b.Axioms, a.Axioms)
		addH, delH := setDiff(hypKeys(b), hypKeys(a))
		addL, delL := setDiff(b.Local, a.Local)
		if a.Constants == b.Constants && len(addAx)+len(delAx)+len(addH)+len(delH)+len(addL)+len(delL) == 0 {
			continue
		}
		fmt.Fprintf(w, "* `%s`: closure %d → %d (%+d)", a.Target, b.Constants, a.Constants, a.Constants-b.Constants)
		if len(addAx) > 0 {
			fmt.Fprintf(w, "; **axioms entered: %s**", strings.Join(addAx, ", "))
			for _, x := range addAx {
				if !StandardAxioms[x] {
					gate = true
				}
			}
		}
		if len(delAx) > 0 {
			fmt.Fprintf(w, "; axioms left: %s", strings.Join(delAx, ", "))
		}
		if len(addH) > 0 {
			fmt.Fprintf(w, "; **hypotheses entered: %s**", strings.Join(addH, ", "))
			gate = true
		}
		if len(delH) > 0 {
			fmt.Fprintf(w, "; hypotheses discharged: %s", strings.Join(delH, ", "))
		}
		if len(addL)+len(delL) > 0 {
			fmt.Fprintf(w, "; project constants +%d −%d", len(addL), len(delL))
		}
		fmt.Fprintln(w)
	}
	for _, b := range before {
		if !seen[b.Target] {
			fmt.Fprintf(w, "* `%s`: **gone**\n", b.Target)
		}
	}
	return gate
}

func hypKeys(r *Report) []string {
	var ks []string
	for _, h := range r.Hypotheses {
		ks = append(ks, h.Head)
	}
	return ks
}

func setDiff(a, b []string) (added, removed []string) {
	in := func(xs []string) map[string]bool {
		m := map[string]bool{}
		for _, x := range xs {
			m[x] = true
		}
		return m
	}
	ma, mb := in(a), in(b)
	for x := range mb {
		if !ma[x] {
			added = append(added, x)
		}
	}
	for x := range ma {
		if !mb[x] {
			removed = append(removed, x)
		}
	}
	sort.Strings(added)
	sort.Strings(removed)
	return
}
