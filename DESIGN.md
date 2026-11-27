# sloot: streaming and plucking for big Lean 4 developments

Status: design draft, 2026-11-24. Name: `sloot` (Dutch for a drainage ditch, the stream it runs; formerly `lean-pluck`). Alternatives were
in §13.

## 1. Problem

Some Lean developments are too big to build whole on a modest machine.
Alpöge's RH release has 175,187 `.lean` files and about 17M lines on top of
Mathlib. Its author says most of it "is unnecessary". On a public GitHub
runner (4 CPUs, 16 GB RAM, 14 GB SSD, 6 h per job) or a small VPS you cannot
hold every `.olean` at once. You also cannot afford the 5.9 GB whole-Mathlib
export that independent kernels take (see §2.1).

`sloot` is a general, open engine with four jobs:

1. **Stream.** Compile a project module by module in import order. Each
   compiled module is kept only while a later module still imports it, so
   disk use stays bounded.
2. **Record.** Store Lean's real dependency graph, as elaborated, from each
   module's `.olean` data as soon as that module is compiled.
3. **Pluck.** For chosen target theorems, compute their closure. Emit a
   minimal source tree, the axioms used, and a **bin** holding everything
   that was cut.
4. **Export.** Optionally export only the plucked closure so independent
   kernels can check it.

## 2. Prior art, and what each piece lacks

Sources were read on 2026-11-24. Anything marked *(unverified)* comes from
memory and was not confirmed in a primary source today.

### 2.1 Kernel-level checking

| Tool | What it covers | What it lacks for stream+pluck |
|---|---|---|
| **lean4export** ([repo](https://github.com/leanprover/lean4export), [format 3.1.0](https://github.com/leanprover/lean4export/blob/master/format_ndjson.md)) | Writes NDJSON: a `meta` header, then names, levels and exprs as integer-indexed records, then axiom, def, thm, opaque, quot and inductive records. Usage: `lake env lean4export Mod+ [-- decl…]`. Exporting a module includes its transitive closure. Böving confirmed on Zulip that an export of chosen constants contains only their transitive closure ([Arena thread](https://leanprover-community.github.io/archive/stream/113488-general/topic/Lean.20Kernel.20Arena.html)). | Records **no module and no source position**, and no attributes, instances or notation. It is kernel-only: good for checking, useless for producing source. It also needs the full `.olean` closure loaded. |
| **lean4checker** ([repo](https://github.com/leanprover/lean4checker)) | Replays each module's new constants into the kernel. Its README says it is "not an external verifier"; it is there to catch environment hacking. Archived 2026-03-25. It has shipped in the toolchain as `leanchecker` since v4.28.0. The 4.33.1 source (`src/lean/LeanChecker.lean`) reads all three olean parts with `readModuleDataParts` and replays the most private one. | Uses the same kernel as Lean. Works per module over a full build, with no target-directed mode. |
| **`lake check` / `lake comparator`** ([v4.35.0 notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/), released 2026-10-12) | `lake check` builds, exports, replays in a separate process and rejects non-standard axioms. It builds inside bubblewrap. `--paranoid` adds every bundled checker; `--from-export` takes an existing export. `lake comparator` checks that each named solution theorem has the same statement as the challenge. The 4.35 toolchain bundles **lean4lean, nanoda, con-leche, con-ron** and `leanchecker-paranoid`. 4.35 also removed `Lean.trustCompiler`, `reduceBool` and `reduceNat` (#14953). | Whole project, no streaming, no plucking. It is 4.35+, while the targets here (riemann on 4.33.0-rc2, Alpöge on 4.33.1) predate it. It is the **checking back end** we hand plucked exports to once a project is on 4.35. |
| **nanoda_lib** ([repo](https://github.com/ammkrn/nanoda_lib)) | A Rust kernel that reads lean4export output from a file or stdin. Configured by a JSON file: `permitted_axioms`, `unpermitted_axiom_hard_error`, `nat_extension`, `string_extension`, `num_threads`, `pp_declars`. | Needs an export. |
| **lean4lean** ([repo](https://github.com/digama0/lean4lean)) | A Lean port of the C++ kernel, with partial verification (`Lean4Lean.Verify`). Checks `.olean` files directly: `lean4lean [--fresh] [--compare] [MOD]`. | Derived from the C++ kernel, so it may share its bugs (README). |
| **Lean Kernel Arena** ([arena.lean-lang.org](https://arena.lean-lang.org/), run by Breitner since Jan 2026) | Benchmarks dozens of checkers. The Mathlib export is **5.9 GB**. The official kernel takes 33.7 min and 9.9 GB; nanoda 16 min and 5.9 GB; con-leche 17 min; the fastest Rust checkers about 1–2 min and 2–5 GB. | Shows the problem: a whole-library export is at or over a runner's RAM. A plucked export is the natural input. |
| **con-leche / con-ron** ([reference: External Kernels](https://lean-lang.org/doc/reference/latest/External-Kernels/)) | FRO kernels in Lean and in Rust. con-leche has a machine-checked proof that any environment it accepts has a set-theoretic model. | Export-based, like the others. |

### 2.2 Dependency and import tools

| Tool | What it covers | What it lacks |
|---|---|---|
| **`lake shake`** (in core; source `src/lean/lake/Lake/CLI/Shake.lean`, Carneiro and Ullrich) | Minimises imports at **module** level. For each module it folds the constants in its own constants' types and values, plus the `extraModUses` entries. Those entries record elaboration-time module uses (attributes, notation, instances, meta imports) that terms do not show. It loads the environment with `loadExts := false` and only works on `module`-system files. Mathlib CI notes that "with the arrival of the module system, the old `shake` is no longer functional" (`build_template.yml`). | Module granularity only: it never removes a declaration. It needs the whole closure loaded at once. |
| **`Lean.ExtraModUses`** (core, `Lean/ExtraModUses.lean`) | `recordExtraModUse` and `recordIndirectModUse` store elaboration dependencies that are invisible in terms. They are saved in the **private** olean part. | Module-level, so it is coarse for plucking. It is the best signal we have for source re-elaboration, though, and we use it (§5.3). |
| **import-graph** ([repo](https://github.com/leanprover-community/import-graph)) | `lake exe graph`, `unused_transitive_imports`, `#min_imports`, `#find_home`, `#show_imports`, and `findTransitiveImportsFromSource` (imports read from source without a build). | Module level, apart from per-command `#show_imports`. No declaration closure. |
| **`Lean.Name.transitivelyUsedConstants`** and ad-hoc scripts ([Zulip, Dec 2025](https://leanprover-community.github.io/archive/stream/239415-metaprogramming-/-tactics/topic/Theorem-level.20dependency.20graph.html)) | Topaz computed a theorem's closure and the unused constants of one project (211 of them) by running a script at the end of the main file. | Needs the whole environment loaded. Produces no source and no bin, and does not scale. |
| **kim-em/lean-minimizer** ([repo](https://github.com/kim-em/lean-minimizer)) | `lake exe minimize file.lean`: delta debugging with dependency analysis, command deletion, import inlining and `sorry` replacement, rechecking by elaboration after each step. Built for **bug-report test cases**. | Single file, elaborates repeatedly, slow by design. No sound "same theorem" contract: it keeps a marker, not a statement. |
| **Tree shaking thread** ([Zulip 2023–24](https://leanprover-community.github.io/archive/stream/113488-general/topic/Tree.20shaking.html)) | Commelin asked for a deterministic tree shaker ("ZeroToReal in 6000 lines"). The thread lists what breaks when you drop imports or declarations: instances (resolution changes path), attributes and tactic-only uses, notation ("expected token"), and stale oleans. | Never built. Those failure modes are our §5.3. |
| **LeanDojo** ([repo](https://github.com/lean-dojo/LeanDojo)) and **Pantograph** ([PyPantograph](https://github.com/stanford-centaur/PyPantograph), core `leanprover/Pantograph`) | Extraction for ML: tactic states, premises, constant inspection. Original LeanDojo is deprecated in favour of LeanDojo-v2. *(unverified: LeanDojo traces by building the whole repo with an instrumented extractor, which costs a full build.)* | Whole-repo tracing. Not aimed at minimal sources or bounded disk. |

### 2.3 Build, cache and CI

| Tool | What it covers | What it lacks |
|---|---|---|
| **Lake** (4.33.1 `lake --help`, `lake help build`) | Module targets with facets (`lake build +Mod:olean`, `:ilean`, `:c`, `:deps`, or a source path `Foo/Bar.lean:o`). `lake env` sets `LEAN_PATH` for a tool. Per module, Lake writes a `--setup` JSON (`name`, `package`, `isModule`, `options`, `importArts`, `plugins`, `dynlibs`); for `module` files, `importArts` maps each import to its artifacts, and a streamer driving `lean` directly has to produce the same file. Also `build`, `query`, `env`, `lean`, `shake`, `pack`/`unpack`, and `cache get/put/add/stage/unstage/put-staged`. The Lake cache is content-addressed (input hash to output artifact hashes, JSONL per package, `~/.cache/lake`), with S3-compatible remotes scoped by `--scope` or `--repo`. 4.34–4.35 added `--package` to `cache get/put` and `lake build`. | Lake rebuilds whatever is missing. It has no notion of "delete once no longer needed", so a streamer must drive `lean` directly (§4), using Lake only to resolve packages and fetch caches. |
| **Mathlib cache** ([Cache/README.md](https://github.com/leanprover-community/mathlib4/blob/master/Cache/README.md)) | `lake exe cache get [files]` fetches `.ltar` bundles (olean, ilean, trace, c, hash) per file. A file hash combines the root hash, path, content and import hashes. Passing files fetches only their import closure. | Mathlib-specific, though `lake cache` is set to replace it. Mathlib CI sets `LAKE_NO_CACHE` because the two are incompatible. |
| **Mathlib CI** (`.github/workflows/build_template.yml` in the pinned Mathlib) | Builds on self-hosted Hoskinson runners (`runs_on: pr`) inside a **landrun** sandbox with no network, then **stages** the cache. Upload happens in a separate job on a disposable `ubuntu-latest` runner. `leanchecker` runs daily, not per PR ("quite expensive for little benefit"). | Relies on big self-hosted machines and the full 6.1 GB olean tree. It is still the pattern to copy for trust: build sandboxed, upload separately. |

### 2.4 What is genuinely new here

* **Bounded-disk streaming.** Delete compiled output once its last transitive
  dependent has compiled, and order the build to keep that live set small.
  No existing tool does this.
* **Declaration-level elaborated graph, recorded per module as it streams.**
  The graph is read straight from that module's own olean parts, without
  loading its imports. Shake does this at module level with everything
  loaded.
* **Source-level pluck with a contract.** The same target statements, the
  same axioms, a stock rebuild that passes, and a repair loop. The minimizer
  does delta debugging for bug reports; the tree-shaking thread asked for this
  and never got it.
* **The bin**: an indexed record of everything cut and why.
* **Closure-only exports** routed to the kernels that 4.35 bundles. This is
  the piece that makes independent checking fit on a standard runner.
* **A resumable, chunked CI pipeline** as a reusable GitHub workflow.

## 3. Pipeline

```
          ┌──────────┐  modules.json   ┌──────────┐ decls/*.jsonl ┌─────────┐
 sources ─▶  plan    ├────────────────▶│  stream  ├──────────────▶│  graph  │
          │(headers) │  order+lastUse  │ lean -o  │  (extractor)  │  store  │
          └──────────┘                 │ extract  │               └────┬────┘
                                       │ refcount │                    │
                                       │ delete   │              targets│
                                       └──────────┘                    ▼
   ┌─────────┐  plucked tree  ┌─────────┐   tree + bin   ┌──────────────────┐
   │ verify  │◀───────────────│ repair  │◀───────────────│ pluck (closure,  │
   │(stream  │   failures ───▶│  loop   │                │  command map,    │
   │ rebuild)│                └─────────┘                │  policies)       │
   └────┬────┘                                           └──────────────────┘
        │ statements + axioms match
        ▼
   ┌─────────┐ closure.ndjson ┌───────────────────────────────┐
   │ export  ├───────────────▶│ kernels: leanchecker, nanoda, │
   └─────────┘                │ lean4lean, con-leche/ron, …   │
                              └───────────────────────────────┘
```

**Plan.** Parse only the header of every source file (`module`, `prelude`,
`[public] [meta] import [all] M`), as `findTransitiveImportsFromSource` does.
Build the import DAG. Restrict it to the import closure of the target modules:
for Alpöge, that is whatever `Main.lean` transitively imports, not all 175k
files. Choose a compile order and compute `lastUse` for each module (§4).
Dependencies that have a cache (Mathlib) are **fetched for the needed closure
only**, never built.

**Stream.** For each module in order:
1. Make sure its imports' outputs are present: in the local store, or fetched
   from cache.
2. Run `lean` the way Lake would. The recipe is the `.lake/.../M.trace` log
   (`LEAN_PATH=… lean -R root -o M.olean -i M.ilean [--setup …] M.lean`),
   with C output disabled.
3. Run the **extractor** (§5.1) on the module's fresh `.olean`,
   `.olean.server` and `.olean.private`, appending to `graph/decls/M.jsonl`.
4. Decrement reference counts and delete every module whose `lastUse` is
   this step.
5. Write the state file (§8.2).

**Graph** stays on disk as sharded JSONL plus a compact index, small next to
the oleans (§7.1).

**Pluck.** Compute the closure, map constants to source commands, apply the
policies, write the tree and the bin (§5).

**Verify.** Stream-compile the plucked tree with stock Lean. Compare target
statements and axioms against the recorded originals. On failure, restore
from the bin and repeat (§5.4).

**Export and check** (optional, §6).

## 4. Reference-counted outputs

**Key fact.** Lean loads the transitive import closure of a module when it
elaborates it. Under the module system some imports are loaded as `.ir` only
(`EffectiveImport.hasData` in `Lean/Environment.lean`), so the closure is an
*upper bound* on what must be present. A module's outputs are kept live
until the last module that **transitively** imports it has compiled. That is
always safe; direct imports alone are not enough. Phase 2 measures how much a
finer, module-system-aware liveness (data vs IR only) would save.

Notation: compile set `S` (the import closure of the targets) and an order
`π` (a topological order of `S`).

* `lastUse(m) = max { π(d) : d ∈ S, m ∈ closure(d) }`. Targets and
  explicitly kept modules get `lastUse = ∞`.
* After compiling module `π⁻¹(t)`, delete every `m` with `lastUse(m) = t`.
  That covers `.olean*`, `.ilean` and `.ir`, and the `.c` file, which is never
  produced.
* Live bytes at step `t` are `Σ size(m)` over `π(m) ≤ t < lastUse(m)`.
* **Lower bound, whatever the order:** `max_m (size(closure(m)) + size(m))`.
  You cannot compile `m` without its closure present. Base modules such as
  `Mathlib.Order.Basic` stay live almost to the end. The design promises
  *peak ≈ the largest single closure*, not *peak ≈ a single module*.
  `sloot plan` prints that bound and the predicted peak for the chosen
  order before anything runs.
* **Ordering heuristic.** List scheduling over the DAG. Among ready modules,
  pick the one that retires the most live bytes (makes the most `lastUse`
  hits), break ties by finishing the current subtree (DFS-postorder flavour),
  and use estimated sizes until real ones are known. With `k` parallel
  workers the peak grows; the scheduler enforces a byte budget by holding a
  ready module back if starting it would exceed the budget.
* **The IR must stay.** Modules that define tactics, elaborators or
  `initialize` blocks are run by later modules' elaboration, so their `.ir`
  shares their `lastUse`. They count like any other output.
* **The cache is not the live set.** The *store* holds live outputs. A
  content-addressed *cache* (the local Lake cache dir, S3 via `lake cache`,
  or GitHub `actions/cache`) may hold more, under its own size cap with LRU
  eviction. Keys follow Lake and Mathlib: `H(toolchain, path, content,
  sorted import keys)`. A cache miss means a recompile, never a wrong answer,
  because keys are content hashes and Lean also checks olean headers.
* **Upstream packages with a public cache** (Mathlib, Batteries, …) are never
  compiled. Their closure is fetched (`lake exe cache get <files>` or
  `lake cache get`) into the store under the same refcounting. They are
  deleted when dead and refetched if a later replan needs them.
* **Extraction happens before deletion.** It is the only time a module's
  private olean part is guaranteed to exist.

## 5. Dependencies and plucking

### 5.1 Reading the elaborated dependencies

Three ways were considered:

| Source | Pros | Cons |
|---|---|---|
| (a) `importModules` and walk `Environment.constants` | Simple; full API (attributes, instances) | Loads the whole closure: Mathlib-size RAM and minutes per call, and it cannot stream. |
| (b) **Per-module `readModuleDataParts`** on `M.olean`, `.olean.server`, `.olean.private` (the way `LeanChecker.lean` does it) | Needs **no imports**, so cost scales with one module. The most private part has all constants with their full values. `entries` holds each extension's raw entries for this module. | Extension entries are opaque (`EnvExtensionEntry`) and must be decoded per known extension with `unsafeCast` against a pinned toolchain. |
| (c) The export (lean4export) | Kernel-exact and independent of Lean internals | No module, no source position, no attributes. Needs the closure loaded. |

**Choice: (b) as the streaming extractor, with (a) as a fallback and
cross-check.** The extractor is a small Lean program, `lean/Extract.lean`,
compiled once per toolchain. For each module it emits one JSON record per
constant:

```json
{"n":"Nat.succ_le_of_lt","k":"thm","m":"Mathlib.Order.Basic",
 "ty":["LT.lt","LE.le","Nat.succ",…], "val":[…],          // foldConsts, split
 "aux_of":null,                      // parent for _proof_i, match_i, eq_i, _simp_…, _private…
 "rng":[412,0,415,23],               // declRangeExt entry (when present)
 "attrs":["simp"], "inst":false, "meta":false, "size":{"ty":31,"val":402}}
```

It also emits a per-module record: `imports` with their
`public`/`meta`/`all` flags, `extraModUses`, `indirectModUses`, the
extensions with non-empty entries, and which parsers, macros and elaborators
(keyed declaration attributes) the module registers.

Two rules learned from the sources:

* **Use the most private part** for constants. Under the module system the
  public `.olean` is the exported view, and theorem bodies may be absent
  there. `LeanChecker.lean` says the most private part "subsumes all prior
  ones".
* **Reserved names** (equation lemmas `f.eq_1`, `_simp_…`) are regenerated on
  demand. Fold them into their base declaration, as shake's
  `getDepConstName?` does.

### 5.2 The kernel closure

`K(T)` is the least set containing the targets `T` and closed under:

* type and value constants (`foldConsts`);
* inductive families: an inductive type pulls its constructors, recursor,
  `casesOn`/`recOn`/`below`/`brecOn`/`noConfusion` (all generated by one
  command anyway), and the mutual `all` group;
* structures: projections and the structure-eta auxiliaries;
* `Quot` primitives and the prelude, which are always present.

`K(T)` is exactly what an export of `T` contains, and it is all a kernel
needs. **Axioms used** = `K(T) ∩ axioms`, which gives the same answer as
`CollectAxioms`, computed in Go, with a per-target listing.

### 5.3 From constants to source: the elaboration closure

Source has to *re-elaborate*, and the elaborator needs things that leave no
trace in terms. Work at **command granularity**:

1. **Command map.** Each constant maps to the source command that created
   it, using `declRangeExt`; aux constants map through `aux_of`. One command
   can create many constants (`structure`, `inductive`, `to_additive`,
   `@[simps]`, `deriving`, `instance`, `mutual`). Keeping the command keeps
   them all; the extras go to the bin's "kept as collateral" count.
2. **Scaffolding is always kept** in any file that keeps something:
   `namespace`/`section`/`end`, `open`, `variable`, `universe`,
   `set_option`, `noncomputable section`, `local notation`, and
   `attribute [local …]`.
3. **Meta modules are kept whole.** A module whose `entries` register
   parsers, syntax, macros, elaborators, tactics, simprocs, attributes or
   `initialize` blocks — anything that changes how *later* files parse or
   elaborate — is kept whole whenever any kept module imports it through the
   kept import graph or lists it in `extraModUses`. Meta code is small next to
   theory, so this costs little and removes a whole class of failures.
4. **Policy for attribute-driven automation.** In kept theory modules:
   * `minimal`: commands in `K(T)` only. Instances and simp lemmas that were
     actually used appear in the terms, so they are already in `K(T)`.
   * `default`: also keep, in kept modules, instances whose class is in
     `K(T)`, plus `@[simp]`, `@[ext]`, `@[norm_cast]`, `@[fun_prop]` and
     similar lemmas whose head symbols are all in `K(T)`. Re-running `simp`
     with a slightly different simp set is the main source of breakage.
   * `module`: keep every module in the closure whole. Only files are
     dropped. This is the safe fallback.
5. **Anonymous commands are binned.** `example`, `#check`, `#eval`,
   `#print`, `#guard_msgs` and similar define no constant, so nothing can
   need them, but they may mention binned names. The first verify on
   riemann-overlay failed for exactly this reason: `example`s in `Fiber.lean`
   used binned lemmas. They go to the bin with reason "anonymous command".
   `attribute [...] x` commands whose names were all binned get the same
   treatment (phase 3).
6. **Imports of plucked files** become the original imports minus modules
   that are now empty, with their imports transitively re-exported where
   needed. Afterwards, `lake shake --fix` can be run on `module`-system files
   as an optional tidy-up.
7. **Provenance.** Each plucked file starts with a comment block giving the
   original path, content hash, line count, kept and removed counts, and the
   bin path.

### 5.4 Repair loop

The plucked tree is **untrusted output**. Verification is a stock
stream-compile of the tree. On a failure at module `M`, command `c`:

| Error | Restore from the bin |
|---|---|
| unknown identifier/constant `x` | the command defining `x` |
| failed to synthesize `C …` | instances of `C` from `M`'s import closure in the bin |
| `simp` / `simp_all` / `norm_num` made no progress or failed | the attribute-tagged lemmas binned from modules in `M`'s closure, by head symbol |
| parse error / expected token | the module that defines the syntax (whole) |
| anything else, or the same command twice | `M`'s original text whole, then its imports whole |

Each round only moves items from the bin back into the tree. The bin is
finite, so the loop terminates, and the last fallback is the original source.
Every restore is logged in `pluck.log` with the error that triggered it, so
policies can learn: a restore that recurs becomes a default rule.

**Success means:** the tree builds; for every target, the rebuilt type is
alpha-equal to the recorded one (we compare the export-hash of the type; the
names are the same); and the axioms are a subset of the original ones, which
in practice means equal.

## 6. Export and the trust story

**Export.** `lean4export Mods -- targets…` on the *plucked* tree exports
exactly `K(T)`. That file is small enough for any kernel on a runner. On
toolchains ≥ 4.35, `lake check --from-export=closure.ndjson --paranoid` runs
all bundled kernels. Earlier toolchains need a lean4export built for that
toolchain, plus nanoda and lean4lean built separately.

**What checks what:**

| Step | Trusted / checked by |
|---|---|
| Header parse, ordering, refcount, deletion (Go) | **Not trusted, and cannot cause false acceptance.** A missing olean is a load error. A stale one is caught by content-hash keys and Lean's olean header check. |
| Compilation | Stock `lean`: elaborator and C++ kernel, as for any Lean user. It runs untrusted code (tactics, `#eval`, `initialize`), so it runs in a sandbox (bubblewrap, as `lake check` does, or landrun, as Mathlib CI does) with no network and writes limited to the store. |
| Extractor and graph | **Not trusted.** A wrong graph can only make the pluck too small, which fails the rebuild, or too big, which is harmless. |
| Pluck and repair (Go) | **Not trusted.** Its output is rebuilt from scratch by stock Lean. |
| "Same theorem" | The recorded type from the original oleans is compared with the rebuilt one (`comparator`-style; on 4.35+, `lake comparator` with the original as challenge). **Phase-1 limit:** the prototype compares a 32-bit structural hash of the target's own type, not the definitions the type mentions, and passes no lakefile `leanOptions` to `lean`. Next steps are to compare `th` for every kept project constant (cheap), and then to do a real comparator-style check of the statement's definitional closure. |
| Axioms | Computed twice: once from the graph, once in a rebuilt environment (`CollectAxioms`). Both must agree. |
| Kernel acceptance | `leanchecker` replay, then independent kernels on the closure export. Disagreement is reported, not voted away. The Arena guide warns that it is not by itself proof of unsoundness. |
| lean4export faithfulness | Covered by diversity: several kernels with different code bases (Rust, Lean, set-theoretic model proof) read the same file. The residual risk is an exporter bug that drops a constant, which would surface as an unknown constant in the kernels. |
| Meaning of the statements | **Humans.** The plucked tree is what makes this review feasible. Readers check the target statements and the *definitions they mention*, which is a few files instead of 17M lines. The bin index lets a reviewer confirm nothing relevant was cut. |

## 7. Output formats

### 7.1 Graph store (`graph/`)

* `modules.jsonl`: name, file, content hash, imports with flags,
  `extraModUses`, sizes of each olean part, compile seconds and peak RSS.
* `decls/<Module>.jsonl`: per-constant records (§5.1).
* `index.bin`: a dense name-id table and CSR adjacency, rebuilt by Go from
  the JSONL. Mathlib has about 10⁶ constants with aux names; at 4 bytes per
  edge this is a few hundred MB, so it fits in a runner.

### 7.2 Pluck (`out/<pluck-name>/`)

* `src/…`: the plucked tree, with `lakefile.toml`, `lean-toolchain` and the
  `lake-manifest.json` of the original, pinned.
* `PLUCK.json`: targets with type-hashes, axioms per target, counts (modules
  and commands kept/removed, lines before/after), policy, and repair rounds.
* `axioms.txt`: a human-readable list, one target per block.

### 7.3 The bin (`out/<pluck-name>/bin/`)

Everything the pluck cut. It serves review, restoring, and (in the project owner's words) "a good
source for jokes".

* `bin/index.jsonl`, one record per removed command:
  ```json
  {"decls":["Foo.bar","Foo.bar_aux"],"kind":"theorem","module":"Proj.Foo",
   "file":"Proj/Foo.lean","lines":[120,188],"bytes":4211,"term_size":90211,
   "statement":"theorem Foo.bar (x : ℕ) : …",       // pretty-printed type, truncated
   "reason":"unreachable",             // or "unreachable-from-targets-but-used-by:Foo.baz (also binned)",
                                       // "policy:minimal-dropped-simp", "whole-module-dead"
   "nearest_kept":"Foo.qux",           // closest kept decl in the same file, for context
   "restore":"pluck restore Foo.bar"}
  ```
* `bin/modules.jsonl`: files removed entirely, with line counts and the
  reason (no constant reached, not meta).
* `bin/src/<path>.lean` (optional, `--bin-source`): the removed text, kept
  in file order with `-- [bin] lines a–b of …` markers. This makes restoring
  exact.
* `bin/REPORT.md`: totals and top lists. The 50 largest unreachable proofs by
  term size, files where ≥ 99 % was cut, the longest declaration names, the
  most elaborate proof of something trivial, and theorems that are never used
  but have "main" or "key" in their name. This is where the jokes live.
* `pluck restore <decl|module>` moves an item from the bin back into the tree
  and records the restore in `PLUCK.json`.

### 7.4 Export (`out/<pluck-name>/export/`)

`closure.ndjson` (lean4export format 3.1.0, zstd-compressed at rest) and
`kernels.json`: per kernel, its version, verdict, time and RSS.

### 7.5 Claim pricing: closure reports, diffs, queries

These outputs are first-class because riemann-overlay's work is *pricing
claims*: what each theorem rests on (`CLAIMS.md`, `PRICES.md`,
`STATEMENTS.md`, the session gate). They are generic. Any project that
states results under hypotheses gets the same use from them.

**Closure report, per theorem** (`sloot report`, Markdown plus JSON):

* **Axioms**: the axioms in `K(T)`, with the non-standard ones flagged.
  Anything beyond `propext`, `Classical.choice` and `Quot.sound` counts as
  non-standard. That covers a project's own axioms, such as riemann's
  `Assumptions.lean`, and `Lean.ofReduceBool`/`trustCompiler` before 4.35.
* **Hypotheses**: the ∀-binders of the statement whose type is a
  proposition. The test is that the binder's head constant has a type ending
  in `Prop`, recorded by the extractor as `rp`. Each one is listed with its
  head and marked *project-defined* when the head comes from the project or a
  vendored package. That is how `RiemannHypothesis` shows up: as a hypothesis
  `h`, never as an axiom. Instance binders and data parameters are listed
  separately.
* **What it leans on**: closure constants per package (`Riemann`, `Zeta23`
  (vendored), `Mathlib`, `Init`, …), the project and vendored modules
  touched, the project and vendored constants by name, and the Mathlib areas
  by count (`Analysis.SpecialFunctions`, `NumberTheory.LSeries`, …).
* **Size**: constants in the closure, total term size, and (after a cut)
  the source lines kept.

**Diff between two commits** (`sloot diff A.json B.json`). For each
theorem it reports whether the closure grew or shrank, which axioms and
hypotheses entered or left, and how many project constants were added or
removed. It exits non-zero when a non-standard axiom or a new hypothesis
enters, which makes it a ready check for a session gate. With the query store
(§11), the same diff is a `dolt diff` between two analysed commits.

**Query** (`sloot why X Y`). "Does `X` depend on `Y`?" The answer
yes comes with a shortest dependency path, each step tagged with its module.
Every step also says whether the use is in the *statement* or the *proof*,
because a hypothesis that enters through a definition in a statement prices
differently from a lemma used in a proof.

## 8. GitHub Actions

### 8.1 Fitting a runner

Standard Linux runners ([docs](https://docs.github.com/en/actions/reference/runners/github-hosted-runners)):
public repos get 4 CPU, 16 GB RAM and 14 GB SSD; private repos get 2 CPU,
8 GB RAM and 14 GB SSD. Each job may run 6 h. The cache allows 10 GB per repo
and a matrix allows 256 jobs per run
([limits](https://docs.github.com/en/actions/reference/limits)). The design
targets **the private runner (2 CPU, ~7 GB usable RAM, 14 GB disk)** so that
it fits everyone.

* **Module batches per job.** A job takes the next slice of `π` and runs
  until a *time budget* (default 5 h 15 m) or a *disk budget* is hit. It then
  writes the state and uploads.
* **Store between jobs.** Live outputs go to `actions/cache` under keys
  `lp-<toolchain>-<module-hash>` (one entry per module, or per "layer" of
  modules with the same `lastUse` range to keep the entry count down). The
  state file lists the live keys. A job restores only the keys its batch's
  closures need. When a module dies, the next job deletes its key
  (`gh cache delete`, `actions: write`). **That is the refcount in CI.**
  Upstream caches (Mathlib) are refetched per job for the needed closure and
  never stored in `actions/cache`.
* **Peak check.** `plan` refuses, or splits further, if the predicted live
  set exceeds the cache budget (default 8 of the 10 GB) or the runner disk.
* **Graph shards** are small and go up as workflow artifacts (or are
  committed to a `pluck-data` branch). Pluck, verify and export run in later
  jobs on the graph alone, plus the compile closure of the plucked tree,
  which is small by construction.
* **Kernels** run as a matrix, one job per kernel, on `closure.ndjson`.

### 8.2 Resumable state file

`pluck-state.json` holds the toolchain, project commit, plan hash, order `π`,
cursor, `lastUse` table, live keys with sizes, finished graph shards, and
per-module timings. A job is idempotent with respect to it. If a job dies,
the next one restarts from the last committed cursor; modules already in the
store or cache are skipped. Chaining:

* **Within one run:** a fixed fan of `needs:`-linked stages is generated from
  the plan (`plan` prints the number of batches).
* **Across runs**, for runs longer than one workflow: the last job re-triggers
  the workflow with `workflow_dispatch`. Events created by `GITHUB_TOKEN` do
  not start new runs, *except* `workflow_dispatch` and `repository_dispatch`
  *(unverified wording; to confirm in GitHub docs before Phase 5)*. Each run
  restores `pluck-state.json` from the previous run's artifact.

### 8.3 Reusable workflow

The public toolkit repo ships `.github/workflows/pluck.yml` with
`on: workflow_call`. Inputs: `project-path`, `targets`, `policy`, `kernels`,
`batch-minutes`, `bin-source`. Outputs: links to the pluck and bin artifacts.
A project calls it with

```yaml
jobs:
  pluck:
    uses: <org>/sloot/.github/workflows/pluck.yml@v1
    with: { targets: "Main.rh_of_X Main.grh_of_Y", policy: default, kernels: "nanoda,lean4lean" }
    permissions: { actions: write, contents: read }
```

The called workflow runs in the **caller's** repository context, so
visibility follows the caller.

### 8.4 Visibility and licence

**A project without a licence must run in a private repository.** Job logs,
artifacts and caches of a public repo are readable by anyone. Ours contain
source excerpts (error messages, the plucked tree, `bin/src`, pretty-printed
statements). Publishing those is redistribution, and an unlicensed release
gives no right to redistribute. This applies to Alpöge's release: a
private fork of it calls the public reusable workflow, and all
artifacts stay private. Public projects with an open licence get free
minutes and the larger 4-CPU, 16 GB runner. The toolkit repo itself is public. Its own CI runs only on open fixtures: a
Mathlib slice, synthetic tests, and **riemann-overlay** (Apache-2.0 code), the
public test bed. A workflow in the toolkit repo checks out riemann-overlay at
a pinned commit and plucks and reports on it without writing to it.

## 9. CLI sketch

```
sloot plan    --project DIR --targets Mod.thm,… [--order greedy|topo] [--budget 10G]
                   → plan.json: compile set, order, lastUse, predicted peak, lower bound
sloot stream  --plan plan.json --store DIR [--jobs 2] [--time 5h15m] [--state pluck-state.json]
                   compiles, extracts, deletes; resumable
sloot graph   --store DIR [--from-oleans LEAN_PATH]   # extract from an existing build (no compile)
sloot closure --graph DIR --targets … [--why NAME]    # K(T), axioms, explanation path
sloot cut     --graph DIR --targets … --policy minimal|default|module --out DIR [--bin-source]
sloot verify  --pluck DIR [--repair N]                # stream-compile, compare, repair loop
sloot restore --pluck DIR NAME|MODULE
sloot export  --pluck DIR [--exporter PATH]
sloot check   --pluck DIR --kernels leanchecker,nanoda,lean4lean,con-leche,con-ron
sloot report  --targets … [--local R] [--vendor Z] [--json F]   # closure report (§7.5)
sloot diff    A.json B.json | --dolt C1 C2           # closure diff; exit 1 on new axioms/hypotheses
sloot why     X Y                                     # does X depend on Y? path, statement/proof tagged
sloot relations --out DIR                             # CSV relations (§11.1) for Dolt / Datalog
sloot query   FILE.dl | -e 'rule…'                    # Datalog over the relations, with derivations
sloot find    'PATTERN' [--within T]                  # Loogle, joined with the relations
sloot run     …                                       # all of the above
sloot gha     plan|batch|finish                       # CI helpers used by pluck.yml
```

Go handles orchestration, scheduling, the graph, the pluck, the bin and the
reports. Lean handles `Extract.lean` (olean parts to JSONL) and
`Compare.lean` (type hashes and axioms in a rebuilt environment). Both are
compiled per toolchain into `~/.cache/sloot/<toolchain>/`.

## 10. Phased plan

* **Phase 1, prototype (this repo now).** The Go CLI with `graph`,
  `closure`, `why`, `report`, `diff` and `cut`, and the Lean extractor using
  per-module `readModuleDataParts`. The open test bed is riemann-overlay
  (public, Apache-2.0 code,
  github.com/LaPingvino/riemann-overlay). Its prebuilt oleans (Mathlib and
  vendored zeta23 included, toolchain 4.33.0-rc2) are read **read-only**;
  nothing is written into that repo. The prototype produces a closure report
  for a headline theorem (`Riemann.proportion_of_RH_zeta`: RH as a
  hypothesis), plucks it to a source tree of Riemann files with a bin, and
  verifies the cut by compiling the plucked files against the stock Mathlib
  and zeta23 oleans in a scratch store.
  **Phase 1 findings (2026-11-24, riemann-overlay, toolchain 4.33.0-rc2):**
  * Per-module extraction works as designed. It reads the three olean parts
    without loading imports. Theorem bodies of `module`-system files (Mathlib)
    come from the private part. The import closure of `Riemann.RH` (10,641
    modules: core, Batteries, Mathlib, zeta23 and Riemann) was extracted in
    11 min 43 s on a machine at load 25–50, into a 112 MB gzip store. That
    is about 2 % of the 6.1 GB of Mathlib oleans.
  * `Riemann.proportion_of_RH_zeta` has 70,167 constants in its closure:
    Mathlib 59,837, Init 7,589, Zeta23 2,422, Riemann 130. Only the three
    standard axioms appear, and `RiemannHypothesis` shows up as hypothesis
    `h`. This agrees with the repo's own `audit/PrintAxioms.lean` claim.
    `why` finds the route into vendored zeta23 through `zetaFamily` (used in
    the statement), then `zetaNonempty` (proof), then
    `Zeta23.RiemannVonMangoldt.main`.
  * The source cut covers the 12 of 14 Riemann files in the target's import
    closure. It keeps 86 commands and bins 758, 3 of them anonymous
    `example`s. Lines go from 16,748 to 3,571, and four files are emptied
    down to their imports. 310 binned commands are used by nothing else in the
    graphed import closure. Files outside that closure (`Capacity`,
    `Optimal`) are not counted, so this is an upper bound on "dead code".
  * **Verify passed** on the second attempt. The first failed on `example`s
    that use binned lemmas, which led to rule 5 of §5.3. Stock `lean`
    4.33.0-rc2 compiled all 12 plucked files against the untouched Mathlib
    and zeta23 oleans in 74 min of wall clock on a machine at load 15–20
    (`Riemann.Assumptions` alone took 22 min). The target's statement hash
    and axioms (`Classical.choice`, `Quot.sound`, `propext`) are unchanged.
    No repair round was needed.
  * Loading the whole store into Go maps takes about 2 min per command. The
    dense `index.bin` of §7.1 (name ids and CSR adjacency) is the next fix.
* **Phase 1b, relations.** `sloot relations` emits the §11.1 tables as
  CSV (done for `decl`, `uses`, `axiom`, `imports` and `extra_use`). They come straight from the graph, so they arrive early.
* **Phase 2, streaming.** `plan` and `stream` with refcounted deletion,
  measured on a Mathlib slice compiled from source (for example the closure
  of `Mathlib.Data.Real.Basic`): predicted against actual peak.
* **Phase 3, deep pluck.** Pluck into Mathlib's own files (policies,
  repair loop), so the output is self-contained without Mathlib. Commelin's
  "ZeroToReal" is a good public benchmark.
* **Phase 4, export and kernels.** Closure export plus nanoda, lean4lean and
  leanchecker on 4.33; `lake check --from-export --paranoid` once projects
  move to ≥ 4.35.
* **Phase 5, CI.** The reusable workflow, state file, cache refcounting and
  chained runs. The first public caller is riemann-overlay: the toolkit repo's
  workflow runs against it (closure reports, bin, diff per push). It is open
  and licensed, so its logs and artifacts may be public.
* **Phase Q, query layer** (§11). Dolt store with one commit per analysed
  project commit; `query` with Mangle, benchmarked against jaala; `find`
  through Loogle; riemann-overlay's registers as saved claim queries. Whether
  its session gate adopts them is that repo's decision.
* **Phase 3W, pull mode** (§12): a coordinator hands out work units, and
  idle machines pull them, in the style of SETI@home or Folding@home.
* **Phase 6, Alpöge.** Run from a private fork of the release, which
  owns its own targets and reports. sloot just gets bug reports. The
  first heavy run uses `scripts/desktop-run.sh` on one big machine. It runs
  one command with resumable phases: build, extract, report, pluck, verify,
  then publish to a results branch of the fork. That runner is the first
  worker in waiting (§12.6).

## 11. Query layer: relations, Dolt, Datalog, statement search

The graph is already relational, so the extractor's records map straight onto
tables. Phase 1 already emits them as CSV (`sloot relations`). That export has been
loaded into Dolt with `dolt table import`, and the recursive closure query
ran on it.
The database and the Datalog front end come after the prototype (phase Q).

### 11.1 Relations

| relation | columns | from |
|---|---|---|
| `decl` | name, kind, module, line, end_line, type_size, value_size, type_hash, returns_prop | per-constant record |
| `uses` | from, to, where ∈ {`statement`, `proof`, `value`} | `ty` / `val` lists (inductive companions count as `statement`) |
| `axiom` | name | `decl.kind = axiom` |
| `hypothesis` | theorem, binder, head, project_defined | the `stmt` records of chosen (or all project) theorems |
| `attribute` | decl, attr | decoded extension entries: `simp`, `instance`, `ext`, … (phase 3 extractor work) |
| `imports` | module, imported, public, meta, all | module record |
| `extra_use` | module, used_module, public, meta | `extraModUses` |
| `module` | name, package, file, is_module, olean_bytes | module record and the store |
| `binned` | pluck, decl, reason | cut output |
| `claim` | id, theorem, register, expected_axioms, expected_hypotheses | the project's registers (§11.5) |

### 11.2 Store: Dolt

The store is a Dolt database with **one Dolt commit per project commit
analysed**. The Dolt commit message is the project commit hash, and the tag is
the session number. This was checked locally with Dolt 2.7.6: `WITH
RECURSIVE` works as is, so a closure with its path is one query:

```sql
WITH RECURSIVE dep(n, path) AS (
  SELECT 'Riemann.proportion_of_RH_zeta', CAST('Riemann.proportion_of_RH_zeta' AS CHAR(4000))
  UNION ALL
  SELECT u.`to`, CONCAT(dep.path, ' > ', u.`to`) FROM dep JOIN uses u ON u.`from` = dep.n)
SELECT DISTINCT n FROM dep JOIN axiom ON axiom.name = dep.n;
```

`dolt diff <c1> <c2> uses decl hypothesis`, or the `dolt_diff('c1','c2','uses')`
table function inside SQL, gives the raw closure diff. Both were checked on a
scratch database.
`sloot diff --dolt` turns it into the per-theorem summary of §7.5.
For Mathlib-scale graphs (about 10⁷ `uses` rows) the recursive CTE is the
slow path. The Go closure engine stays the fast path, and Dolt is the
history, diff and ad-hoc layer. Dolt is already in use around this project,
so there is nothing new to operate.

### 11.3 Datalog front end

This is for rule-style questions that SQL makes painful:

```prolog
depends(X, Z)     :- uses(X, Z, _).
depends(X, Z)     :- uses(X, Y, _), depends(Y, Z).
rests_on(T, A)    :- depends(T, A), axiom(A).
assumes(T, H)     :- hypothesis(T, _, H, _).
assumes(T, H)     :- depends(T, L), hypothesis(L, _, H, _), uses(T, L, statement).
price(T, A)       :- rests_on(T, A), !standard(A).            % "price of a claim"
```

Answers carry a **derivation** ("why"): the rule instances and base facts
that produced each tuple.

Engines compared (2026-11-24):

| engine | form | recursion / negation / aggregation | provenance | maturity |
|---|---|---|---|---|
| **Mangle** ([repo](https://github.com/google/mangle), [engine docs](https://pkg.go.dev/github.com/google/mangle/engine)) | embeddable Go library, Apache-2.0 | yes / *(negation unverified: the README shows only `!=`)* / yes (`group_by`, `fn:Count`) | not documented; there is a `provenance` dir in the repo but its contents are unconfirmed | about 3k stars, used by several projects, started at Google and now independent (Codeberg primary) |
| **jaala** ([pkg](https://pkg.go.dev/github.com/panyam/jaala)) | embeddable Go library, Apache-2.0 | yes / stratified / yes | **native**: each answer row cites its facts, plus an optional derivation tree. Also queries *across versions* of the facts and shows what changed | pre-1.0 (v0.1.104), young, small user base |
| swdunlop `seminaive` ([pkg](https://pkg.go.dev/swdunlop.dev/pkg)) | small Go package | basic | none | small |
| **Soufflé** ([provenance paper](https://arxiv.org/abs/1907.05045)) | C++ compiler/interpreter, separate binary | full | native: minimal-height proof trees (Zhao, Subotić and Scholz). The exact CLI flag *(`-t explain`, unverified)* was not confirmed | mature, the fastest at scale. Not embeddable in Go; separate process and compile step |

**Pick: Mangle**, as an embedded library behind a small `Engine` interface.
The reasons:

1. A tool that feeds trust decisions should rest on the most-used engine.
   **Caveat:** `price` needs stratified negation, and Mangle's support for it
   is unverified. Phase Q1 checks it first. If it is missing, jaala (which
   documents stratified negation) becomes the pick.
2. Derivations for our rules are cheap to add ourselves. We stamp each derived
   fact with the iteration it first appeared in, then rebuild a minimal-height
   proof by choosing, for each tuple, a rule instance whose body facts are all
   from earlier iterations. That is the Soufflé paper's construction, and it
   is engine-agnostic.
3. It keeps everything in one Go binary.

jaala is the one to beat: its native provenance and version diffs match our
needs exactly. Phase Q1 benchmarks it against Mangle on riemann's relations
(results checked against the SQL CTE) and switches if it wins. Soufflé is the
batch fallback if both Go engines are too slow at Mathlib scale. We export
the same relations as `.facts` files; no lock-in.

### 11.4 Statement shapes: reuse Loogle

**Loogle** ([repo](https://github.com/nomeata/loogle)) already does
type-pattern search. It runs as `loogle [--json] [--module M] [--path P]
'(List.replicate (_ + _) _ = _)'` over *any Lake project of the same
toolchain* and caches its index next to the root olean. We reuse it rather
than rebuild it. `sloot find PATTERN [--within T]` runs Loogle in
JSON mode on the project (or the plucked tree) and joins the hits with the
relations. That allows queries such as "statements shaped like `_ ≤ _ * N` in
the closure of `T`", or "binned theorems with this shape". **LeanSearch**
([paper](https://arxiv.org/abs/2403.13310), leansearch.net) and its
successors (LeanExplore, Lean Finder) do natural-language semantic search
over Mathlib. They are hosted and Mathlib-centred, so they serve as an
optional "find me the Mathlib lemma" link, not as part of the engine. They
are never used on private (unlicensed) code.

### 11.5 For riemann-overlay: registers as saved queries

Each register row (`CLAIMS.md` grade-A certificates, `PRICES.md` priced
entries, `STATEMENTS.md` axioms and hypotheses) becomes a `claim` row: an id,
the certificate theorem(s), and the expected axioms and hypotheses. The
session gate then:

1. analyses the new commit (a Dolt commit);
2. re-runs every saved claim query (closure report and price rules);
3. diffs against the previous session, and fails on a claim whose axioms or
   hypotheses changed without a register edit, or whose certificate vanished.

The registers keep their prose. The queries make the "graded A" column
mechanically re-checkable every session. Adding such a gate to
riemann-overlay is that repo's own decision, made under its `LOOP.md` and
`METHOD.md`. This design only provides the tool.

## 12. Pull mode: idle workers, SETI/Folding@home style

Instead of one machine running the pipeline from start to finish, the work
is cut into **units**. A coordinator hands out a unit only when all of its
inputs exist, so the work moves through the import graph like a wave. Workers
pull units only while their machine is idle.

### 12.1 Work units

| unit | inputs | outputs |
|---|---|---|
| `build(batch)` | sources of the batch (hashes); outputs of every module in the batch's import closure (cache keys) | `.olean*`/`.ilean`/`.ir` per module (content-addressed) |
| `extract(batch)` | outputs of the batch | graph shards (`decls/<Module>.jsonl.gz`) |
| `pluck(targets)` | all shards in the closure | plucked tree, bin, report |
| `verify(pluck, batch)` | plucked sources of the batch; rebuilt outputs of its imports | rebuilt outputs, statement and axiom comparison |
| `check(export, kernel)` | closure export | kernel verdict |

Batches are the same slices of the order `π` that the CI design uses (§8):
a module set whose imports lie in earlier batches, sized to about an hour of
work on a typical worker. Each unit is keyed by the hash of its declared
inputs, so the same unit always has the same id and can be deduplicated.

### 12.2 Coordinator

The coordinator holds the queue, the input/output table and the state of
every unit (`waiting`, `ready`, `leased(worker, until)`, `done(hash)`). It
also holds the reference count of every output (§4), and deletes an output
from its blob store once the last unit that needs it is done. Three
interchangeable back ends:

* **A small HTTP service** on the project's VPS. It is Go, uses the same Dolt
  store as §11, keeps blobs on disk or in S3-compatible storage, and issues
  leases with deadlines.
* **A git branch as the queue.** Units are files under `queue/ready/`. A
  worker claims one by pushing a commit that moves it to `queue/leased/`;
  push races resolve themselves because a rejected push means someone else
  won. Results go to `results/` (small) or to a release or bucket (large).
  This needs no server, which suits a project that has only a GitHub repo.
* **GitHub issues or Actions** as the queue: an issue per unit and a label as
  its state. This is the simplest to watch, but rate limits make it suitable
  only for coarse units.

The coordinator never runs Lean. It schedules by readiness, leases with a
timeout (an expired lease is handed out again), and prefers units whose
outputs unblock the most others, which keeps the wave front wide.

### 12.3 Workers

* **Installation:** a single static Go binary (`sloot worker`) plus
  elan, at user level. On Linux it runs as a systemd **user** service, on
  macOS as a launchd agent. No root access.
* **Idle detection:** load average below a threshold over a few minutes,
  screen locked or the session idle (logind `IdleHint` on Linux, `ioreg`
  HIDIdleTime on macOS), on AC power (not battery), and enough free disk.
* **Politeness:** `nice -n 19` plus `ionice -c 3`, a cap of
  `nproc − reserve` threads, and a cap on RAM through cgroup v2
  `MemoryMax` when systemd allows it. On user activity the worker **pauses**
  the job (SIGSTOP on the process group) and resumes it later (SIGCONT). If
  the pause outlasts the lease, it hands the unit back.
* **Local cache:** a worker keeps the outputs it has produced or fetched, up
  to a disk budget, and the coordinator prefers to give it units whose inputs
  it already holds (affinity). This cuts transfer, which matters more than
  CPU for Mathlib-sized imports.

### 12.4 Results and deduplication

A worker uploads its outputs under content hashes along with a small
manifest: unit id, input hashes, output hashes, toolchain, timings and peak
RSS. The coordinator stores each blob once. A second, identical result for the
same unit costs only the manifest.

### 12.5 Trust: workers are never trusted

* **Builds and extracts** are run **redundantly** on at least two
  independent workers, and only matching outputs are accepted. Olean files
  are not bit-for-bit reproducible across machines in every case, so the
  comparison is semantic. It uses the extracted shard (names, kinds, type
  hashes, dependency lists), which is deterministic given the constants. A
  mismatch triggers a third run and flags the workers involved.
* **The final authority is the kernel.** Whatever the workers did, the
  plucked closure is exported and checked by the independent kernels (§6) on
  a machine the project owner trusts, or on several. A forged olean or shard
  can at worst cause a wrong pluck, and that fails the rebuild or the kernel
  check. It cannot cause a false acceptance.
* **Sandboxing on the worker side** follows the same rule as in CI
  (bubblewrap or landrun, no network, writes only to the unit's directory).
  Compiling a Lean project runs its code.

### 12.6 Volunteers and privacy

* **Open mode:** for a public, licensed Lean project, anyone can run a
  worker and lend cycles. Redundancy (§12.5) is mandatory in this mode.
* **Private mode:** for a project without a licence, or a private one, only
  the owner's own workers take part. They authenticate to the coordinator, and
  no unit, log or blob leaves the owner's machines and private storage. This
  is the same licence rule as in §8.4.
* **The desktop runner as the first worker.** `scripts/desktop-run.sh` is
  monolithic today, but its phases are already units in the sense of §12.1,
  each resumable and recorded in a state file. The migration path is to have
  it ask a coordinator "what is ready for me?" before each phase, with
  batches instead of whole phases. Its state file then becomes the lease
  record. I did not build that now: it would delay a runner that is useful as
  it is.

## 13. Names

Chosen: `sloot`. The old working name was `lean-pluck`. Alternatives considered:

* **winnow**: separating grain from chaff, and the chaff is the bin.
* **lean-thresh**
* **sieve**
* **gleaner**

My pick is **winnow** (CLI `winnow`, bin = `chaff/`) if the name is free on
Reservoir. Otherwise keep `sloot`.
