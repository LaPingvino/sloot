package project

import (
	"os"
	"testing"
)

// Runs only where the riemann-overlay build is present.
func TestRiemannClosure(t *testing.T) {
	root := "/home/joop/Projects/riemann"
	tc := root + "/.lake/elan/toolchains/leanprover--lean4---v4.33.0-rc2"
	if _, err := os.Stat(tc); err != nil {
		t.Skip("no riemann build here")
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
