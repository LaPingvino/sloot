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

	"github.com/LaPingvino/lean-pluck/internal/graph"
	"github.com/LaPingvino/lean-pluck/internal/project"
)

// Verify compiles the plucked tree with stock `lean`, module by module in
// import order, into out/build (never into the project), against the
// dependencies' existing oleans. It then re-extracts the rebuilt modules and
// checks, for every target, that the statement fingerprint is unchanged and
// that the axioms are the same.
func Verify(g *graph.Graph, p *project.Project, out, extractor string, pluckRoots map[string]bool, log io.Writer) error {
	var res Result
	b, err := os.ReadFile(filepath.Join(out, "PLUCK.json"))
	if err != nil {
		return err
	}
	if err := json.Unmarshal(b, &res); err != nil {
		return err
	}
	lib := filepath.Join(out, "build", "lib", "lean")
	// search path: the rebuilt tree first, then every package except the
	// plucked ones (whose original oleans must not be used)
	paths := []string{lib}
	for _, pk := range p.Packages {
		if pk.Name == "root" {
			continue
		}
		paths = append(paths, pk.Lib)
	}
	leanPath := strings.Join(paths, ":")
	lean := filepath.Join(p.Toolchain, "bin", "lean")
	srcRoot := filepath.Join(out, "src")
	var jobs []graph.Job
	for _, mod := range res.Modules {
		rel := filepath.Join(strings.Split(mod, ".")...)
		src := filepath.Join(srcRoot, rel+".lean")
		olean := filepath.Join(lib, rel+".olean")
		jobs = append(jobs, graph.Job{Mod: mod, OLean: olean})
		if st, err := os.Stat(olean); err == nil {
			if ss, err := os.Stat(src); err == nil && !st.ModTime().Before(ss.ModTime()) {
				fmt.Fprintf(log, "verify: %s up to date\n", mod)
				continue
			}
		}
		os.MkdirAll(filepath.Dir(olean), 0o755)
		t0 := time.Now()
		cmd := exec.Command(lean, "-R", srcRoot, "-o", olean, "-i", strings.TrimSuffix(olean, ".olean")+".ilean", src)
		cmd.Env = append(os.Environ(), "LEAN_PATH="+leanPath, "LEAN_NUM_THREADS=3")
		msg, err := cmd.CombinedOutput()
		fmt.Fprintf(log, "verify: compiled %s in %s\n", mod, time.Since(t0).Round(time.Second))
		if err != nil {
			os.WriteFile(filepath.Join(out, "verify.log"), msg, 0o644)
			return fmt.Errorf("plucked %s does not compile (see verify.log): %s", mod, firstLines(string(msg), 8))
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
	for _, mod := range res.Modules {
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
