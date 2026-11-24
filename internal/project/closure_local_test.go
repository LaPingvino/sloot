package project

import (
	"os"
	"testing"
)

// Runs against a built riemann-overlay checkout when
// LEAN_PLUCK_TEST_PROJECT (the checkout) and LEAN_PLUCK_TEST_TOOLCHAIN (the
// toolchain directory that built it) are set.
func TestRiemannClosure(t *testing.T) {
	root, tc := os.Getenv("LEAN_PLUCK_TEST_PROJECT"), os.Getenv("LEAN_PLUCK_TEST_TOOLCHAIN")
	if root == "" || tc == "" {
		t.Skip("LEAN_PLUCK_TEST_PROJECT / LEAN_PLUCK_TEST_TOOLCHAIN not set")
	}
	p, err := Load(root, tc)
	if err != nil {
		t.Fatal(err)
	}
	order, _, err := p.ImportClosure([]string{"Riemann.RH"})
	if err != nil {
		t.Fatal(err)
	}
	missing := 0
	for _, m := range order {
		if _, _, ok := p.OLean(m); !ok {
			missing++
			if missing < 5 {
				t.Logf("no olean: %s", m)
			}
		}
	}
	t.Logf("closure of Riemann.RH: %d modules, %d without olean", len(order), missing)
	if missing > 0 {
		t.Fail()
	}
}
