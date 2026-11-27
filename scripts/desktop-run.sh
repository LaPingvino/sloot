#!/usr/bin/env bash
# desktop-run.sh — one-command heavy run of sloot on the private Alpöge
# fork, meant for a big desktop (≈2 TB disk, 64 GB RAM).
#
#   bash desktop-run.sh [WORKDIR]          (default WORKDIR: ~/lean-work)
#
# Phases, each resumable (re-running skips finished phases; the long ones are
# incremental themselves):
#   prereqs → clone → toolchain → cache → build → tools → extract → pluck → publish
#
# It:
#   * installs elan (user-level, ~/.elan, no sudo) and, if needed, Go (into
#     WORKDIR/tools) when they are missing;
#   * clones or updates sloot and the private fork into WORKDIR;
#   * fetches Mathlib's cache at the fork's pin, builds the whole release
#     niced and on all cores but $RESERVE (default 2);
#   * extracts the declaration graph of every module into WORKDIR/store;
#   * writes the closure report for $TARGET (default riemannHypothesis), plucks
#     it and verifies the plucked tree with lake;
#   * commits the store and the reports to branch results/<date> of the fork
#     and pushes it;
#   * logs to WORKDIR/run.log, keeps per-phase times in WORKDIR/state, prints
#     a summary with disk use.
# It deletes nothing outside WORKDIR, and inside it only its own temporary
# files. The build stays on disk for the next run.
#
# Environment overrides: FORK_URL, PLUCK_URL, PLUCK_REF, TARGET, RESERVE,
# GO_VERSION, SKIP_PUSH=1 (commit but do not push).
set -euo pipefail

WORK=$(mkdir -p "${1:-${LEAN_WORK:-$HOME/lean-work}}" && cd "${1:-${LEAN_WORK:-$HOME/lean-work}}" && pwd)
FORK_URL=${FORK_URL:-git@github.com:LaPingvino/alpoge-lean-shake.git}
PLUCK_URL=${PLUCK_URL:-git@github.com:LaPingvino/sloot.git}
PLUCK_REF=${PLUCK_REF:-main}
TARGET=${TARGET:-riemannHypothesis}
RESERVE=${RESERVE:-2}
GO_VERSION=${GO_VERSION:-1.27.4}

FORK=$WORK/alpoge-lean-shake
PLUCK=$WORK/sloot
STORE=$WORK/store
OUT=$WORK/out/$TARGET
STATE=$WORK/state
LOG=$WORK/run.log
TOOLS=$WORK/tools
mkdir -p "$TOOLS" "$WORK/out"
touch "$STATE"
exec > >(tee -a "$LOG") 2>&1

export PATH="$HOME/.elan/bin:$TOOLS/go/bin:$PATH"
NPROC=$( (command -v nproc >/dev/null && nproc) || sysctl -n hw.ncpu 2>/dev/null || echo 4)
JOBS=$(( NPROC > RESERVE + 1 ? NPROC - RESERVE : 1 ))
NICE=(nice -n 15)
command -v ionice >/dev/null && NICE=(ionice -c 3 nice -n 15)
PIN=()
if command -v taskset >/dev/null; then PIN=(taskset -c "0-$((JOBS - 1))"); fi
export LEAN_NUM_THREADS=$JOBS   # Lake's job count and Lean's thread count

say()  { printf '\n== %s  %s\n' "$(date '+%F %T')" "$*"; }
die()  { say "FAILED: $*"; echo "Log: $LOG"; exit 1; }
done_phase() { grep -q "^$1 done " "$STATE"; }
run_phase() {   # run_phase NAME FUNCTION — skipped when already done
  local name=$1 fn=$2 t0
  if done_phase "$name"; then say "$name: already done, skipping"; return 0; fi
  say "$name: start"
  t0=$(date +%s)
  # run in a subshell that is not in a tested context, so `set -e` applies
  # inside the phase (it would be ignored under `fn || die`)
  local rc
  set +e
  ( set -e; "$fn" )
  rc=$?
  set -e
  [ "$rc" = 0 ] || die "phase $name (exit $rc; re-run the script to resume)"
  echo "$name done $(( $(date +%s) - t0 ))s $(date '+%F %T')" >> "$STATE"
  say "$name: done in $(( $(date +%s) - t0 ))s"
}

# ---------------------------------------------------------------- phases
prereqs() {
  for c in git curl tar; do command -v $c >/dev/null || { echo "missing: $c (please install it)"; return 1; }; done
  if ! command -v elan >/dev/null; then
    echo "installing elan into ~/.elan (user-level, no PATH changes to your shell files)"
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none --no-modify-path
  fi
  if ! command -v go >/dev/null; then
    local os arch
    os=$(uname -s | tr A-Z a-z); arch=$(uname -m)
    case $arch in x86_64) arch=amd64 ;; aarch64|arm64) arch=arm64 ;; esac
    echo "installing Go $GO_VERSION into $TOOLS/go"
    curl -sSfL "https://go.dev/dl/go${GO_VERSION}.${os}-${arch}.tar.gz" | tar -xz -C "$TOOLS"
  fi
  git ls-remote "$FORK_URL" >/dev/null || { echo "cannot reach $FORK_URL (ssh key / access?)"; return 1; }
  local free
  free=$(df -Pk "$WORK" | awk 'NR==2 {print int($4/1024/1024)}')
  echo "free disk at $WORK: ${free} GB; cores: $NPROC, using $JOBS"
  [ "$free" -ge 300 ] || echo "WARNING: under 300 GB free; the full build may not fit"
}

sync_repo() {   # sync_repo URL DIR REF
  if [ -d "$2/.git" ]; then
    git -C "$2" fetch --quiet origin
    git -C "$2" checkout --quiet "$3"
    git -C "$2" merge --ff-only --quiet "origin/$3" || echo "note: $2 has local commits; not fast-forwarded"
  else
    git clone --quiet "$1" "$2"
    git -C "$2" checkout --quiet "$3"
  fi
}
clone() {
  sync_repo "$PLUCK_URL" "$PLUCK" "$PLUCK_REF"
  sync_repo "$FORK_URL" "$FORK" main
  echo "sloot at $(git -C "$PLUCK" rev-parse --short HEAD), fork at $(git -C "$FORK" rev-parse --short HEAD)"
}

toolchain() {
  elan toolchain install "$(cat "$FORK/lean-toolchain")"
}
tcdir() { (cd "$FORK" && dirname "$(dirname "$(elan which lean)")"); }

cache() {
  (cd "$FORK" && lake exe cache get)
}

build() {
  # lake is incremental: an interrupted build resumes here
  (cd "$FORK" && "${NICE[@]}" "${PIN[@]}" lake build)
}

tools() {
  local tc ex
  tc=$(cat "$FORK/lean-toolchain")
  ex=$WORK/extractor/${tc//[:\/]/_}
  mkdir -p "$ex"
  cp "$PLUCK/lean/Extract.lean" "$PLUCK/lean/lakefile.toml" "$ex/"
  echo "$tc" > "$ex/lean-toolchain"
  (cd "$ex" && lake build)
  mkdir -p "$WORK/bin"
  (cd "$PLUCK" && go build -o "$WORK/bin/sloot" ./cmd/sloot)
  ln -sf "$ex/.lake/build/bin/pluck-extract" "$WORK/bin/pluck-extract"
}

# module roots of the fork: top-level directories and files under its srcDir
roots() {
  local src
  src=$FORK/$(sed -n 's/^srcDir *= *"\(.*\)"/\1/p' "$FORK/lakefile.toml" | head -1)
  (cd "$src" && ls -1 | sed -n 's/\.lean$//p; /\./!p' | sort -u | paste -sd, -)
}

extract() {
  # resumable: shards newer than their .olean are skipped
  "${NICE[@]}" "$WORK/bin/sloot" graph -project "$FORK" -toolchain "$(tcdir)" \
    -store "$STORE" -extractor "$WORK/bin/pluck-extract" -modules Main -all-local
}

pluck() {
  local r
  r=$(roots)
  echo "project module roots: $r"
  # a failed verify is recorded and published, not fatal: the logs are the result
  if "${NICE[@]}" "${PIN[@]}" "$WORK/bin/sloot" pipeline -project "$FORK" -toolchain "$(tcdir)" \
      -store "$STORE" -extractor "$WORK/bin/pluck-extract" -targets "$TARGET" \
      -local "$r" -pluck "$r" -out "$OUT" -bin-source -lake; then
    echo "verified" > "$OUT/VERIFY-STATUS"
  else
    echo "NOT verified (see verify.log)" > "$OUT/VERIFY-STATUS"
  fi
}

publish() {
  local day branch wt sum
  day=$(date +%F)
  branch=results/$day
  wt=$WORK/results-worktree
  git -C "$FORK" fetch --quiet origin
  if [ ! -d "$wt" ]; then
    if git -C "$FORK" ls-remote --exit-code --heads origin "$branch" >/dev/null; then
      git -C "$FORK" worktree add --quiet -B "$branch" "$wt" "origin/$branch"
    else
      git -C "$FORK" worktree add --quiet -B "$branch" "$wt" origin/main
    fi
  fi
  mkdir -p "$wt/results/$day"
  # reports, plucked sources, bin; not the build directories
  tar -C "$WORK/out" --exclude='.lake' --exclude='build' -cf - "$TARGET" | tar -C "$wt/results/$day" -xf -
  # the store, compressed and split under GitHub's 100 MB file limit
  rm -f "$wt/results/$day"/store.tar.*
  if command -v zstd >/dev/null; then
    tar -C "$WORK" -cf - store | zstd -q -T0 -19 | split -b 95m - "$wt/results/$day/store.tar.zst."
  else
    tar -C "$WORK" -czf - store | split -b 95m - "$wt/results/$day/store.tar.gz."
  fi
  sum=$wt/results/$day/SUMMARY.md
  summary > "$sum"
  git -C "$wt" add "results/$day"
  git -C "$wt" commit --quiet -m "sloot results $day: $TARGET on $(git -C "$FORK" rev-parse --short HEAD)" || echo "nothing new to commit"
  if [ "${SKIP_PUSH:-0}" = 1 ]; then echo "SKIP_PUSH=1: not pushing"; return 0; fi
  git -C "$wt" push --quiet origin "$branch" || { echo "push failed; push later with: git -C $wt push origin $branch"; return 1; }
  echo "pushed $branch"
}

summary() {
  echo "# sloot desktop run"
  echo
  echo "* host: $(uname -sr), $NPROC cores (used $JOBS), $(free -g 2>/dev/null | awk '/Mem:/ {print $2 " GB RAM"}')"
  echo "* fork: $(git -C "$FORK" rev-parse HEAD)"
  echo "* sloot: $(git -C "$PLUCK" rev-parse HEAD)"
  echo "* toolchain: $(cat "$FORK/lean-toolchain")"
  echo "* target: \`$TARGET\`; verify: $(cat "$OUT/VERIFY-STATUS" 2>/dev/null || echo 'not run')"
  echo
  echo "| phase | seconds | finished |"
  echo "|---|---|---|"
  awk '{print "| " $1 " | " $3 " | " $4 " " $5 " |"}' "$STATE"
  echo
  echo "Disk use:"
  echo '```'
  du -sh "$FORK/.lake" "$STORE" "$WORK/out" "$WORK/extractor" 2>/dev/null
  echo '```'
}

# ---------------------------------------------------------------- main
say "sloot desktop run in $WORK (log: $LOG)"
run_phase prereqs   prereqs
run_phase clone     clone
run_phase toolchain toolchain
run_phase cache     cache
run_phase build     build
run_phase tools     tools
run_phase extract   extract
run_phase pluck     pluck
run_phase publish   publish
say "summary"
summary
echo
echo "To run again from scratch for a phase, delete its line from $STATE."
