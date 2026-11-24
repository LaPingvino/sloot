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
	"regexp"
	"strings"
)

// Package is one Lake package of the workspace.
type Package struct {
	Name string
	Dir  string // package directory
	Src  string // source root: Dir joined with the package's srcDir
	Lib  string // .lake/build/lib/lean
}

// Project is a resolved workspace.
type Project struct {
	Root      string
	Toolchain string // directory holding bin/lean
	Packages  []Package
	// PathPackages are the manifest's `path` dependencies, relative to Root.
	PathPackages []string
}

// Load resolves the workspace at root. toolchain is the toolchain directory
// (the one containing bin/lean and lib/lean); it must match the oleans.
func Load(root, toolchain string) (*Project, error) {
	root, _ = filepath.Abs(root)
	p := &Project{Root: root, Toolchain: toolchain}
	// Core: Init, Std, Lean, Lake ship sources and oleans in the toolchain.
	p.Packages = append(p.Packages, Package{Name: "lean4",
		Dir: filepath.Join(toolchain, "src", "lean"), Src: filepath.Join(toolchain, "src", "lean"), Lib: filepath.Join(toolchain, "lib", "lean")})
	p.Packages = append(p.Packages, Package{Name: "lake",
		Dir: filepath.Join(toolchain, "src", "lean", "lake"), Src: filepath.Join(toolchain, "src", "lean", "lake"), Lib: filepath.Join(toolchain, "lib", "lean")})
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
			p.PathPackages = append(p.PathPackages, pk.Dir)
		}
		p.Packages = append(p.Packages, Package{Name: pk.Name, Dir: dir, Src: filepath.Join(dir, SrcDir(dir)),
			Lib: filepath.Join(dir, ".lake", "build", "lib", "lean")})
	}
	p.Packages = append(p.Packages, Package{Name: "root", Dir: root, Src: filepath.Join(root, SrcDir(root)),
		Lib: filepath.Join(root, ".lake", "build", "lib", "lean")})
	return p, nil
}

var srcDirRe = regexp.MustCompile(`(?m)^\s*srcDir\s*(?:=|:=)\s*"([^"]*)"`)

// SrcDir reads the package-level `srcDir` from a lakefile.toml or
// lakefile.lean (default "."). Only the package's own setting is read; a
// per-library srcDir is not supported yet.
func SrcDir(dir string) string {
	for _, f := range []string{"lakefile.toml", "lakefile.lean"} {
		b, err := os.ReadFile(filepath.Join(dir, f))
		if err != nil {
			continue
		}
		text := string(b)
		if f == "lakefile.toml" {
			if i := strings.Index(text, "\n["); i >= 0 {
				text = text[:i] // package table only, before the first [section]
			}
		} else {
			// the `package … where` block only: stop at the first library,
			// executable, script or attribute that follows it
			i := strings.Index(text, "package ")
			if i < 0 {
				return "."
			}
			text = text[i:]
			for _, stop := range []string{"lean_lib", "lean_exe", "script ", "@[", "target ", "require "} {
				if j := strings.Index(text, stop); j > 0 {
					text = text[:j]
				}
			}
		}
		if m := srcDirRe.FindStringSubmatch(text); m != nil {
			return m[1]
		}
		return "."
	}
	return "."
}

// LocalModules lists every module whose source is under the root package's
// source directory.
func (p *Project) LocalModules() ([]string, error) {
	root := p.Packages[len(p.Packages)-1]
	var mods []string
	err := filepath.WalkDir(root.Src, func(path string, d os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() && (d.Name() == ".lake" || d.Name() == ".git") {
			return filepath.SkipDir
		}
		if !d.IsDir() && strings.HasSuffix(path, ".lean") {
			rel, _ := filepath.Rel(root.Src, path)
			if strings.HasPrefix(rel, "lakefile") {
				return nil
			}
			mods = append(mods, strings.ReplaceAll(strings.TrimSuffix(rel, ".lean"), string(filepath.Separator), "."))
		}
		return nil
	})
	return mods, err
}

// Root is the root package.
func (p *Project) RootPackage() *Package { return &p.Packages[len(p.Packages)-1] }

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
		for _, d := range []string{p.Packages[i].Src, p.Packages[i].Dir} {
			f := filepath.Join(d, modPath(mod)+".lean")
			if _, err := os.Stat(f); err == nil {
				return f, true
			}
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
