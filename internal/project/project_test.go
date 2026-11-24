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

func TestSrcDir(t *testing.T) {
	d := t.TempDir()
	os.WriteFile(filepath.Join(d, "lakefile.toml"), []byte("name = \"x\"\nsrcDir = \"src\"\n\n[[lean_lib]]\nname = \"A\"\nsrcDir = \"other\"\n"), 0o644)
	if s := SrcDir(d); s != "src" {
		t.Errorf("toml: got %q", s)
	}
	e := t.TempDir()
	os.WriteFile(filepath.Join(e, "lakefile.toml"), []byte("name = \"x\"\n[[lean_lib]]\nsrcDir = \"other\"\n"), 0o644)
	if s := SrcDir(e); s != "." {
		t.Errorf("lib-level srcDir leaked: %q", s)
	}
}

func TestSrcDirLean(t *testing.T) {
	d := t.TempDir()
	os.WriteFile(filepath.Join(d, "lakefile.lean"), []byte("import Lake\nopen Lake DSL\npackage foo where\n  leanOptions := #[]\n\n@[default_target]\nlean_lib Foo\n\nlean_exe cache where\n  srcDir := \"scripts\"\n"), 0o644)
	if s := SrcDir(d); s != "." {
		t.Errorf("lib-level srcDir leaked from lakefile.lean: %q", s)
	}
	os.WriteFile(filepath.Join(d, "lakefile.lean"), []byte("package foo where\n  srcDir := \"src\"\n\nlean_lib Foo\n"), 0o644)
	if s := SrcDir(d); s != "src" {
		t.Errorf("got %q", s)
	}
}
