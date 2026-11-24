package project

import (
	"os"
	"path/filepath"
	"testing"
)

func TestHeader(t *testing.T) {
	src := `/-
Copyright … import Fake.Comment
-/
module -- trailing comment

public import Mathlib.Data.Nat.Init
import all Foo.Bar
public meta import Baz /- inline -/
import A.B
import C.D

/-! doc -/
theorem x : True := trivial
import NotAnImport
`
	f := filepath.Join(t.TempDir(), "X.lean")
	os.WriteFile(f, []byte(src), 0o644)
	imps, isMod, prelude, err := Header(f)
	if err != nil {
		t.Fatal(err)
	}
	if !isMod || prelude {
		t.Fatalf("module=%v prelude=%v", isMod, prelude)
	}
	want := []Import{
		{Mod: "Mathlib.Data.Nat.Init", Public: true},
		{Mod: "Foo.Bar", All: true},
		{Mod: "Baz", Public: true, Meta: true},
		{Mod: "A.B"},
		{Mod: "C.D"},
	}
	if len(imps) != len(want) {
		t.Fatalf("got %+v", imps)
	}
	for i := range want {
		if imps[i] != want[i] {
			t.Errorf("import %d: got %+v want %+v", i, imps[i], want[i])
		}
	}
}
