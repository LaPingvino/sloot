# lean-pluck (working name)

Lean 4 developments can be too large to build whole on a modest machine.
lean-pluck streams them module by module and records the real, elaborated
declaration graph. From that graph it plucks the closure of chosen theorems
into a minimal source tree, and keeps a **bin** of everything it cut.
DESIGN.md has the design, the survey of prior art and the plan. This repo is
in phase 1, a prototype.

## Build

The extractor reads `.olean` files, and those are tied to one exact
toolchain, so it must be built with the toolchain of the project you analyse.
Set that toolchain in `lean/lean-toolchain`, then:

```sh
lake -d lean build                 # → lean/.lake/build/bin/pluck-extract
go build -o bin/lean-pluck ./cmd/lean-pluck
```

## Use (phase 1, on an existing build; nothing is written into the project)

```sh
TC=<toolchain dir>   # the one with bin/lean that built the project
lean-pluck graph    -project P -toolchain $TC -store store -modules Riemann.RH
lean-pluck report   -project P -toolchain $TC -store store -targets Riemann.proportion_of_RH_zeta \
                    -local Riemann -vendor Zeta23 -json report.json
lean-pluck why      -store store Riemann.proportion_of_RH_zeta RiemannHypothesis
lean-pluck cut      -project P -store store -targets … -pluck Riemann -out out/rh -bin-source
lean-pluck verify   -project P -toolchain $TC -store store -out out/rh
lean-pluck diff     before.json after.json
lean-pluck relations -store store -out rel/
```

`lean-pluck pipeline` runs report, cut and verify with a single load of the
store. Add `-lake` to verify the plucked tree with `lake`, which applies the
project's `leanOptions`. `graph -all-local` extracts every module of the root
package.

## Heavy runs

`scripts/desktop-run.sh [WORKDIR]` runs the whole thing on one big machine
with a single command: build, extract, report, pluck, verify, and publish to
a results branch. It is resumable. See the header of the script.
