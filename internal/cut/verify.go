package cut

import (
	"encoding/json"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"time"

	"github.com/LaPingvino/sloot/internal/graph"
	"github.com/LaPingvino/sloot/internal/project"
)

// Verify compiles the plucked tree with stock Lean, never writing into the
// project, then re-extracts the rebuilt modules and checks, for every target,
// that the statement fingerprint and the axioms are unchanged.
//
// Two build modes:
//   - direct (useLake=false): `lean` per module in import order into
//     out/build, against the dependencies' existing oleans. No lakefile
//     options are passed, so this suits projects without `leanOptions`.
//   - lake (useLake=true): the plucked tree under out/src gets the project's
//     lakefile, toolchain and manifest, and `.lake/packages` (and any path
//     packages) symlinked to the project's, so dependencies are reused and
//     the project's `leanOptions` and `moreLeanArgs` apply. Then
//     `lake build +Target…` builds the plucked closure into out/src/.lake.
func Verify(g *graph.Graph, p *project.Project, out, extractor string, useLake bool, log io.Writer) error {
	var res Result
	b, err := os.ReadFile(filepath.Join(out, "PLUCK.json"))
	if err != nil {
		return err
	}
	if err := json.Unmarshal(b, &res); err != nil {
		return err
	}
	tree := filepath.Join(out, "src")
	srcRel, _ := filepath.Rel(p.Root, p.RootPackage().Src)
	srcRoot := filepath.Join(tree, srcRel)
	var lib string
	if useLake {
		lib, err = lakeBuild(g, p, tree, res, log)
		if err != nil {
			return err
		}
	} else {
		lib, err = directBuild(p, out, srcRoot, res, log)
		if err != nil {
			return err
		}
	}
	var jobs []graph.Job
	for _, mod := range res.Modules {
		olean := filepath.Join(lib, filepath.Join(strings.Split(mod, ".")...)+".olean")
		if _, err := os.Stat(olean); err == nil {
			jobs = append(jobs, graph.Job{Mod: mod, OLean: olean})
		}
	}
	vstore := filepath.Join(out, "verify-store")
	if _, err := graph.Extract(extractor, vstore, nil, jobs, log); err != nil {
		return err
	}
	// overlay: drop the original constants of the plucked modules, then load the rebuilt ones
	before := map[string]*graph.Decl{}
	for _, t := range res.Targets {
		before[t] = g.Decls[t]
	}
	origAx := map[string][]string{}
	for _, t := range res.Targets {
		origAx[t] = g.Axioms(g.Close([]string{t}))
	}
	for _, j := range jobs {
		mod := j.Mod
		if m := g.Modules[mod]; m != nil {
			for _, n := range m.Decls {
				delete(g.Decls, n)
			}
			m.Decls = nil
		}
		if err := g.LoadShard(graph.ShardPath(vstore, mod)); err != nil {
			return err
		}
	}
	ok := true
	for _, t := range res.Targets {
		a, b := before[t], g.Decls[t]
		if b == nil {
			fmt.Fprintf(log, "verify: FAIL %s missing after rebuild\n", t)
			ok = false
			continue
		}
		ax := g.Axioms(g.Close([]string{t}))
		same := a.THash == b.THash
		sameAx := strings.Join(ax, ",") == strings.Join(origAx[t], ",")
		fmt.Fprintf(log, "verify: %s statement %s, axioms %s (%s)\n", t, okStr(same), okStr(sameAx), strings.Join(ax, ", "))
		ok = ok && same && sameAx
	}
	if !ok {
		return fmt.Errorf("verification failed")
	}
	return nil
}

func okStr(b bool) string {
	if b {
		return "unchanged"
	}
	return "CHANGED"
}

func firstLines(s string, n int) string {
	ls := strings.SplitN(s, "\n", n+1)
	if len(ls) > n {
		ls = ls[:n]
	}
	return strings.Join(ls, "\n")
}

func directBuild(p *project.Project, out, srcRoot string, res Result, log io.Writer) (string, error) {
	lib := filepath.Join(out, "build", "lib", "lean")
	// search path: the rebuilt tree first, then every package except the
	// root (whose original oleans must not be used)
	paths := []string{lib}
	for _, pk := range p.Packages {
		if pk.Name != "root" {
			paths = append(paths, pk.Lib)
		}
	}
	lean := filepath.Join(p.Toolchain, "bin", "lean")
	for _, mod := range res.Modules {
		rel := filepath.Join(strings.Split(mod, ".")...)
		src := filepath.Join(srcRoot, rel+".lean")
		olean := filepath.Join(lib, rel+".olean")
		if st, err := os.Stat(olean); err == nil {
			if ss, err := os.Stat(src); err == nil && !st.ModTime().Before(ss.ModTime()) {
				fmt.Fprintf(log, "verify: %s up to date\n", mod)
				continue
			}
		}
		os.MkdirAll(filepath.Dir(olean), 0o755)
		t0 := time.Now()
		cmd := exec.Command(lean, "-R", srcRoot, "-o", olean, "-i", strings.TrimSuffix(olean, ".olean")+".ilean", src)
		cmd.Env = append(os.Environ(), "LEAN_PATH="+strings.Join(paths, ":"))
		msg, err := cmd.CombinedOutput()
		fmt.Fprintf(log, "verify: compiled %s in %s\n", mod, time.Since(t0).Round(time.Second))
		if err != nil {
			os.WriteFile(filepath.Join(out, "verify.log"), msg, 0o644)
			return "", fmt.Errorf("plucked %s does not compile (see verify.log): %s", mod, firstLines(string(msg), 8))
		}
	}
	return lib, nil
}

func lakeBuild(g *graph.Graph, p *project.Project, tree string, res Result, log io.Writer) (string, error) {
	for _, f := range []string{"lakefile.toml", "lakefile.lean", "lean-toolchain", "lake-manifest.json"} {
		b, err := os.ReadFile(filepath.Join(p.Root, f))
		if err != nil {
			continue
		}
		if err := os.WriteFile(filepath.Join(tree, f), b, 0o644); err != nil {
			return "", err
		}
	}
	link := func(target, at string) error {
		if _, err := os.Lstat(at); err == nil {
			return nil
		}
		os.MkdirAll(filepath.Dir(at), 0o755)
		return os.Symlink(target, at)
	}
	if err := link(filepath.Join(p.Root, ".lake", "packages"), filepath.Join(tree, ".lake", "packages")); err != nil {
		return "", err
	}
	for _, d := range p.PathPackages {
		if err := link(filepath.Join(p.Root, d), filepath.Join(tree, d)); err != nil {
			return "", err
		}
	}
	args := []string{"-d", tree, "build"}
	seen := map[string]bool{}
	for _, t := range res.Targets {
		if d := g.Decls[t]; d != nil && !seen[d.Mod] {
			seen[d.Mod] = true
			args = append(args, "+"+d.Mod)
		}
	}
	t0 := time.Now()
	cmd := exec.Command(filepath.Join(p.Toolchain, "bin", "lake"), args...)
	cmd.Env = append(os.Environ(), "LAKE_NO_CACHE=1", "PATH="+filepath.Join(p.Toolchain, "bin")+":"+os.Getenv("PATH"))
	msg, err := cmd.CombinedOutput()
	os.WriteFile(filepath.Join(filepath.Dir(tree), "verify.log"), msg, 0o644)
	fmt.Fprintf(log, "verify: lake build of the plucked tree took %s\n", time.Since(t0).Round(time.Second))
	if err != nil {
		return "", fmt.Errorf("plucked tree does not build (see verify.log): %s", lastLines(string(msg), 12))
	}
	return filepath.Join(tree, ".lake", "build", "lib", "lean"), nil
}

func lastLines(s string, n int) string {
	ls := strings.Split(strings.TrimRight(s, "\n"), "\n")
	if len(ls) > n {
		ls = ls[len(ls)-n:]
	}
	return strings.Join(ls, "\n")
}
