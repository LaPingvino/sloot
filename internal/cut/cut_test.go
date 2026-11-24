package cut

import (
	"testing"

	"github.com/LaPingvino/lean-pluck/internal/graph"
)

func TestCommandsGrouping(t *testing.T) {
	g := graph.New()
	add := func(n string, rng []int) {
		g.Decls[n] = &graph.Decl{Name: n, Mod: "M", Rng: rng}
		if g.Modules["M"] == nil {
			g.Modules["M"] = &graph.Module{Name: "M"}
		}
		g.Modules["M"].Decls = append(g.Modules["M"].Decls, n)
	}
	add("S", []int{1, 0, 5, 10})        // structure
	add("S.x", []int{2, 2, 2, 9})       // field: nested span
	add("S.mk", nil)                    // no range: joins S
	add("f", []int{7, 0, 9, 3})         // separate command
	add("_private.M.0.f._proof_1", nil) // private aux of f
	add("g", []int{7, 0, 9, 3})         // same span as f (to_additive)
	cmds := commands(g, "M")
	if len(cmds) != 2 {
		t.Fatalf("want 2 commands, got %d", len(cmds))
	}
	if len(cmds[0].Decls) != 3 || len(cmds[1].Decls) != 3 {
		t.Errorf("grouping: %v / %v", cmds[0].Decls, cmds[1].Decls)
	}
}

func TestSlice(t *testing.T) {
	lines := []string{"abc", "dé f", "ghi"}
	if s := slice(lines, pos{1, 1}, pos{2, 2}); s != "bc\ndé" {
		t.Errorf("got %q", s)
	}
}
