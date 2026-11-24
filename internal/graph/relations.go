package graph

import (
	"encoding/csv"
	"fmt"
	"os"
	"path/filepath"
	"sort"
)

// EdgeWhere says whether `to` occurs in the statement (type) of `from`, or
// only in its proof (theorems) or value (definitions).
func (g *Graph) EdgeWhere(from, to string) string {
	d := g.Decls[from]
	if d == nil {
		return ""
	}
	for _, x := range d.Ty {
		if x == to {
			return "statement"
		}
	}
	for _, x := range d.Ctors {
		if x == to {
			return "statement"
		}
	}
	for _, x := range d.All {
		if x == to {
			return "statement"
		}
	}
	if d.Induct == to {
		return "statement"
	}
	if d.Kind == "thm" {
		return "proof"
	}
	return "value"
}

// WriteRelations writes the graph as CSV relations (DESIGN §11.1), one file
// per relation, with a header row, ready for `dolt table import` or as Datalog
// fact files.
func (g *Graph) WriteRelations(dir string) error {
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return err
	}
	open := func(name string, cols ...string) (*csv.Writer, func() error, error) {
		f, err := os.Create(filepath.Join(dir, name+".csv"))
		if err != nil {
			return nil, nil, err
		}
		w := csv.NewWriter(f)
		w.Write(cols)
		return w, func() error {
			w.Flush()
			if err := w.Error(); err != nil {
				return err
			}
			return f.Close()
		}, nil
	}
	row := func(w *csv.Writer, xs ...any) {
		r := make([]string, len(xs))
		for i, x := range xs {
			r[i] = fmt.Sprint(x)
		}
		w.Write(r)
	}
	names := make([]string, 0, len(g.Decls))
	for n := range g.Decls {
		names = append(names, n)
	}
	sort.Strings(names)
	decl, c1, err := open("decl", "name", "kind", "module", "line", "end_line", "type_size", "value_size", "type_hash", "returns_prop")
	if err != nil {
		return err
	}
	uses, c2, err := open("uses", "from", "to", "where")
	if err != nil {
		return err
	}
	ax, c3, err := open("axiom", "name")
	if err != nil {
		return err
	}
	for _, n := range names {
		d := g.Decls[n]
		line, end := 0, 0
		if len(d.Rng) >= 4 {
			line, end = d.Rng[0], d.Rng[2]
		}
		row(decl, n, d.Kind, d.Mod, line, end, d.TSize, d.VSize, d.THash, d.RetPrp)
		seen := map[string]bool{}
		for _, m := range g.Deps(n) {
			if seen[m] {
				continue
			}
			seen[m] = true
			row(uses, n, m, g.EdgeWhere(n, m))
		}
		if d.Kind == "axiom" {
			row(ax, n)
		}
	}
	imp, c4, err := open("imports", "module", "imported", "public", "meta", "all")
	if err != nil {
		return err
	}
	extra, c5, err := open("extra_use", "module", "used_module", "public", "meta")
	if err != nil {
		return err
	}
	mods := make([]string, 0, len(g.Modules))
	for m := range g.Modules {
		mods = append(mods, m)
	}
	sort.Strings(mods)
	for _, m := range mods {
		for _, i := range g.Modules[m].Imports {
			if len(i) >= 4 {
				row(imp, m, i[0], i[1], i[2], i[3])
			}
		}
		for _, e := range g.Modules[m].Extra {
			if len(e) >= 3 {
				row(extra, m, e[0], e[1], e[2])
			}
		}
	}
	for _, c := range []func() error{c1, c2, c3, c4, c5} {
		if err := c(); err != nil {
			return err
		}
	}
	return nil
}
