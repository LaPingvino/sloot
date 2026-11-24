// Package graph holds the elaborated declaration graph read from the
// extractor's JSONL records, and computes closures and explanation paths.
package graph

import (
	"bufio"
	"compress/gzip"
	"encoding/json"
	"io"
	"os"
	"path/filepath"
	"sort"
	"strings"
)

// Decl is one constant as recorded by pluck-extract.
type Decl struct {
	Name   string   `json:"n"`
	Mod    string   `json:"m"`
	Kind   string   `json:"k"`
	Ty     []string `json:"ty"`
	Val    []string `json:"val"`
	RetPrp bool     `json:"rp"`
	TSize  int      `json:"tsz"`
	VSize  int      `json:"vsz"`
	Ctors  []string `json:"ctors"`
	All    []string `json:"all"`
	Induct string   `json:"induct"`
	Rng    []int    `json:"rng"` // line, col, endLine, endCol (1-based lines)
	THash  string   `json:"th"`  // structural hash of the type (statement fingerprint)
}

// Module is the per-module record.
type Module struct {
	Name     string         `json:"m"`
	IsModule bool           `json:"isModule"`
	Imports  [][]any        `json:"imports"`
	Extra    [][]any        `json:"extra"`
	Exts     map[string]int `json:"exts"`
	Aux      []string       `json:"aux"`
	Decls    []string       `json:"-"`
}

// Graph is the whole store.
type Graph struct {
	Decls   map[string]*Decl
	Modules map[string]*Module
	names   map[string]string // interned names: each name is stored once
}

func (g *Graph) intern(s string) string {
	if t, ok := g.names[s]; ok {
		return t
	}
	g.names[s] = s
	return s
}

func (g *Graph) internAll(xs []string) []string {
	for i, x := range xs {
		xs[i] = g.intern(x)
	}
	return xs
}

// New returns an empty graph.
func New() *Graph {
	return &Graph{Decls: map[string]*Decl{}, Modules: map[string]*Module{}, names: map[string]string{}}
}

// ShardPath is where the records of one module are kept in a store.
func ShardPath(store, mod string) string {
	return filepath.Join(store, "graph", mod+".jsonl.gz")
}

// LoadShard reads one module's records.
func (g *Graph) LoadShard(path string) error {
	f, err := os.Open(path)
	if err != nil {
		return err
	}
	defer f.Close()
	zr, err := gzip.NewReader(f)
	if err != nil {
		return err
	}
	return g.Read(zr)
}

// Read parses extractor JSONL.
func (g *Graph) Read(r io.Reader) error {
	sc := bufio.NewScanner(r)
	sc.Buffer(make([]byte, 1<<20), 1<<28)
	for sc.Scan() {
		line := sc.Bytes()
		var head struct {
			T string `json:"t"`
		}
		if err := json.Unmarshal(line, &head); err != nil {
			return err
		}
		switch head.T {
		case "mod":
			var m Module
			if err := json.Unmarshal(line, &m); err != nil {
				return err
			}
			if old, ok := g.Modules[m.Name]; ok {
				m.Decls = old.Decls
			}
			g.Modules[m.Name] = &m
		case "c":
			var d Decl
			if err := json.Unmarshal(line, &d); err != nil {
				return err
			}
			d.Name, d.Mod, d.Induct = g.intern(d.Name), g.intern(d.Mod), g.intern(d.Induct)
			g.internAll(d.Ty)
			g.internAll(d.Val)
			g.internAll(d.Ctors)
			g.internAll(d.All)
			g.Decls[d.Name] = &d
			m := g.Modules[d.Mod]
			if m == nil {
				m = &Module{Name: d.Mod}
				g.Modules[d.Mod] = m
			}
			m.Decls = append(m.Decls, d.Name)
		}
	}
	return sc.Err()
}

// LoadStore reads every shard in store/graph.
func LoadStore(store string) (*Graph, error) {
	g := New()
	files, err := filepath.Glob(filepath.Join(store, "graph", "*.jsonl.gz"))
	if err != nil {
		return nil, err
	}
	for _, f := range files {
		if err := g.LoadShard(f); err != nil {
			return nil, err
		}
	}
	return g, nil
}

// Deps returns the kernel-level successors of a constant: constants in its
// type and value, plus the structural companions an inductive brings.
func (g *Graph) Deps(n string) []string {
	d := g.Decls[n]
	if d == nil {
		return nil
	}
	out := make([]string, 0, len(d.Ty)+len(d.Val)+len(d.Ctors)+len(d.All)+1)
	out = append(out, d.Ty...)
	out = append(out, d.Val...)
	out = append(out, d.Ctors...)
	out = append(out, d.All...)
	if d.Induct != "" {
		out = append(out, d.Induct)
	}
	return out
}

// Closure is the kernel closure K(T) of the targets.
type Closure struct {
	Set     map[string]bool
	Parent  map[string]string // BFS tree, for explanations
	Missing []string          // referenced but absent from the graph
}

// Close computes K(T).
func (g *Graph) Close(targets []string) *Closure {
	c := &Closure{Set: map[string]bool{}, Parent: map[string]string{}}
	queue := append([]string(nil), targets...)
	for _, t := range targets {
		c.Set[t] = true
	}
	missing := map[string]bool{}
	for len(queue) > 0 {
		n := queue[0]
		queue = queue[1:]
		if g.Decls[n] == nil {
			missing[n] = true
			continue
		}
		for _, m := range g.Deps(n) {
			if !c.Set[m] {
				c.Set[m] = true
				c.Parent[m] = n
				queue = append(queue, m)
			}
		}
	}
	for m := range missing {
		c.Missing = append(c.Missing, m)
	}
	sort.Strings(c.Missing)
	return c
}

// Path returns a dependency path from `from` to `to`, or nil if `to` is not
// in the closure of `from`. Breadth-first, so the path is a shortest one.
func (g *Graph) Path(from, to string) []string {
	c := g.Close([]string{from})
	if !c.Set[to] {
		return nil
	}
	var p []string
	for n := to; ; n = c.Parent[n] {
		p = append(p, n)
		if n == from {
			break
		}
	}
	for i, j := 0, len(p)-1; i < j; i, j = i+1, j-1 {
		p[i], p[j] = p[j], p[i]
	}
	return p
}

// Axioms lists the axioms in a closure, sorted.
func (g *Graph) Axioms(c *Closure) []string {
	var ax []string
	for n := range c.Set {
		if d := g.Decls[n]; d != nil && d.Kind == "axiom" {
			ax = append(ax, n)
		}
	}
	sort.Strings(ax)
	return ax
}

// Root returns the top-level package name of a module (`Mathlib`, `Riemann`, …).
func Root(mod string) string {
	if i := strings.IndexByte(mod, '.'); i >= 0 {
		return mod[:i]
	}
	return mod
}

// Area returns the first two components of a module name (`Mathlib.Analysis`).
func Area(mod string) string {
	parts := strings.SplitN(mod, ".", 3)
	if len(parts) >= 2 {
		return parts[0] + "." + parts[1]
	}
	return mod
}
