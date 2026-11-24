// Package project resolves a Lake workspace into search paths: where each
// module's compiled .olean and its .lean source live. It reads the Lake
// manifest only; it never runs Lake (Lake would rebuild what we delete).
package project

import (
	"bufio"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

// Package is one Lake package of the workspace.
type Package struct {
	Name string
	Dir  string // source root
	Lib  string // .lake/build/lib/lean
}

// Project is a resolved workspace.
type Project struct {
	Root      string
	Toolchain string // directory holding bin/lean
	Packages  []Package
}

// Load resolves the workspace at root. toolchain is the toolchain directory
// (the one containing bin/lean and lib/lean); it must match the oleans.
func Load(root, toolchain string) (*Project, error) {
	root, _ = filepath.Abs(root)
	p := &Project{Root: root, Toolchain: toolchain}
	// Core: Init, Std, Lean, Lake ship sources and oleans in the toolchain.
	p.Packages = append(p.Packages, Package{Name: "lean4",
		Dir: filepath.Join(toolchain, "src", "lean"), Lib: filepath.Join(toolchain, "lib", "lean")})
	p.Packages = append(p.Packages, Package{Name: "lake",
		Dir: filepath.Join(toolchain, "src", "lean", "lake"), Lib: filepath.Join(toolchain, "lib", "lean")})
	var man struct {
		PackagesDir string `json:"packagesDir"`
		Packages    []struct {
			Type, Name, Dir string
		} `json:"packages"`
	}
	b, err := os.ReadFile(filepath.Join(root, "lake-manifest.json"))
	if err != nil {
		return nil, err
	}
	if err := json.Unmarshal(b, &man); err != nil {
		return nil, fmt.Errorf("lake-manifest.json: %w", err)
	}
	if man.PackagesDir == "" {
		man.PackagesDir = ".lake/packages"
	}
	for _, pk := range man.Packages {
		dir := filepath.Join(root, man.PackagesDir, pk.Name)
		if pk.Type == "path" {
			dir = filepath.Join(root, pk.Dir)
		}
		p.Packages = append(p.Packages, Package{Name: pk.Name, Dir: dir,
			Lib: filepath.Join(dir, ".lake", "build", "lib", "lean")})
	}
	p.Packages = append(p.Packages, Package{Name: "root", Dir: root,
		Lib: filepath.Join(root, ".lake", "build", "lib", "lean")})
	return p, nil
}

func modPath(mod string) string { return filepath.Join(strings.Split(mod, ".")...) }

// OLean returns the base .olean path of mod and its package.
func (p *Project) OLean(mod string) (string, *Package, bool) {
	for i := range p.Packages {
		f := filepath.Join(p.Packages[i].Lib, modPath(mod)+".olean")
		if _, err := os.Stat(f); err == nil {
			return f, &p.Packages[i], true
		}
	}
	return "", nil, false
}

// Source returns the .lean source of mod.
func (p *Project) Source(mod string) (string, bool) {
	for i := range p.Packages {
		f := filepath.Join(p.Packages[i].Dir, modPath(mod)+".lean")
		if _, err := os.Stat(f); err == nil {
			return f, true
		}
	}
	return "", false
}

// Import is one import line of a module header.
type Import struct {
	Mod               string
	Public, Meta, All bool
}

// Header parses the import header of a Lean 4 source file: `module`,
// `prelude`, and `[public] [meta] import [all] A B …`, skipping comments.
// It stops at the first token that cannot belong to a header.
func Header(path string) (imports []Import, isModule, isPrelude bool, err error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, false, false, err
	}
	defer f.Close()
	var toks []string
	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 1<<20), 1<<24)
	depth := 0 // nested /- -/ comment depth
	for sc.Scan() {
		line := sc.Text()
		for len(line) > 0 {
			if depth > 0 {
				i, j := strings.Index(line, "-/"), strings.Index(line, "/-")
				if j >= 0 && (i < 0 || j < i) {
					depth++
					line = line[j+2:]
				} else if i >= 0 {
					depth--
					line = line[i+2:]
				} else {
					line = ""
				}
				continue
			}
			c := strings.Index(line, "/-")
			d := strings.Index(line, "--")
			if d >= 0 && (c < 0 || d < c) {
				line = line[:d]
				continue
			}
			if c >= 0 {
				toks = append(toks, strings.Fields(line[:c])...)
				depth++
				line = line[c+2:]
				continue
			}
			toks = append(toks, strings.Fields(line)...)
			line = ""
		}
		if len(toks) > 0 && !headerTok(toks[len(toks)-1], toks) {
			break
		}
	}
	// interpret tokens: `[public] [meta] import [all] A`
	var pending Import // modifiers seen since the last import statement
	var cur Import
	inImport := false
	for _, t := range toks {
		switch {
		case t == "module":
			isModule = true
			inImport = false
		case t == "prelude":
			isPrelude = true
			inImport = false
		case t == "public":
			pending.Public = true
			inImport = false
		case t == "meta":
			pending.Meta = true
			inImport = false
		case t == "import":
			cur = pending
			pending = Import{}
			inImport = true
		case t == "all" && inImport:
			cur.All = true
		case inImport && isIdent(t) && !keywords[t]:
			cur.Mod = t
			imports = append(imports, cur)
			inImport = false // Lean takes one module per `import`
		default:
			return imports, isModule, isPrelude, nil
		}
	}
	return imports, isModule, isPrelude, sc.Err()
}

func headerTok(t string, _ []string) bool {
	switch t {
	case "module", "prelude", "public", "meta", "import", "all":
		return true
	}
	return isIdent(t) && !keywords[t]
}

// keywords end a header: any command that is not part of it.
var keywords = map[string]bool{}

func init() {
	for _, k := range strings.Fields(`theorem lemma def abbrev instance structure class inductive
		namespace section open variable universe set_option noncomputable attribute example axiom
		opaque private protected end macro macro_rules syntax notation infix infixl infixr prefix
		postfix elab elab_rules mutual deriving initialize builtin_initialize partial unsafe
		local scoped omit include export assert_not_exists`) {
		keywords[k] = true
	}
}

func isIdent(t string) bool {
	if t == "" {
		return false
	}
	for _, r := range t {
		if r == '(' || r == ')' || r == ':' || r == '[' || r == '@' || r == '#' || r == '=' {
			return false
		}
	}
	return true
}

// ImportClosure returns the transitive import closure of roots, in a
// topological order (imports before importers), using source headers.
func (p *Project) ImportClosure(roots []string) ([]string, map[string][]Import, error) {
	deps := map[string][]Import{}
	var order []string
	state := map[string]int{} // 1 visiting, 2 done
	var visit func(m string) error
	visit = func(m string) error {
		switch state[m] {
		case 1:
			return fmt.Errorf("import cycle at %s", m)
		case 2:
			return nil
		}
		state[m] = 1
		src, ok := p.Source(m)
		if !ok {
			return fmt.Errorf("no source for module %s", m)
		}
		imps, _, prelude, err := Header(src)
		if err != nil {
			return err
		}
		if !prelude {
			imps = append([]Import{{Mod: "Init", Public: true}}, imps...)
		}
		deps[m] = imps
		for _, i := range imps {
			if err := visit(i.Mod); err != nil {
				return err
			}
		}
		state[m] = 2
		order = append(order, m)
		return nil
	}
	for _, r := range roots {
		if err := visit(r); err != nil {
			return nil, nil, err
		}
	}
	return order, deps, nil
}
