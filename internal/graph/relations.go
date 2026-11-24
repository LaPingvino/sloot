package graph

import (
	"bufio"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"
)

// EdgeWhere says whether `to` occurs in the statement (type) or only in the
// proof/value of `from`.
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
	return "proof"
}

// WriteRelations writes the graph as TSV relations (DESIGN §11.1), one file
// per relation, with a header row, ready for `dolt table import` or Datalog
// `.facts` files.
func (g *Graph) WriteRelations(dir string) error {
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return err
	}
	open := func(name string, cols ...string) (*bufio.Writer, func() error, error) {
		f, err := os.Create(filepath.Join(dir, name+".tsv"))
		if err != nil {
			return nil, nil, err
		}
		w := bufio.NewWriterSize(f, 1<<20)
		fmt.Fprintln(w, strings.Join(cols, "\t"))
		return w, func() error {
			if err := w.Flush(); err != nil {
				return err
			}
			return f.Close()
		}, nil
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
		fmt.Fprintf(decl, "%s\t%s\t%s\t%d\t%d\t%d\t%d\t%s\t%t\n", n, d.Kind, d.Mod, line, end, d.TSize, d.VSize, d.THash, d.RetPrp)
		seen := map[string]bool{}
		for _, m := range g.Deps(n) {
			if seen[m] {
				continue
			}
			seen[m] = true
			fmt.Fprintf(uses, "%s\t%s\t%s\n", n, m, g.EdgeWhere(n, m))
		}
		if d.Kind == "axiom" {
			fmt.Fprintln(ax, n)
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
				fmt.Fprintf(imp, "%s\t%v\t%v\t%v\t%v\n", m, i[0], i[1], i[2], i[3])
			}
		}
		for _, e := range g.Modules[m].Extra {
			if len(e) >= 3 {
				fmt.Fprintf(extra, "%s\t%v\t%v\t%v\n", m, e[0], e[1], e[2])
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
