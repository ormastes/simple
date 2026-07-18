#!/usr/bin/env bash
# Repro: `bin/simple test <spec>` SIGSEGV (139) under concurrent compiler load.
# Lane B4 root-cause harness. Each test run peaks ~1.4GB RSS; N concurrent must
# fit available RAM. The crash is a probabilistic tag-box/pointer-as-int deref in
# the deployed Rust seed interpreter (fault addr 0x11/0x12/0x1b in libc, error 4,
# NO OOM). Concurrency raises the per-invocation hit probability + perturbs heap.
#
# Usage: repro_concurrent_139.sh [N_concurrent] [rounds] [spec]
set -u
B="${SIMPLE_BIN:-/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple}"
N="${1:-12}"
ROUNDS="${2:-2}"
SPEC="${3:-scratch_b4/vanilla_spec.spl}"
cd "$(dirname "$0")/.." || exit 2
mkdir -p scratch_b4/burst
crash=0; total=0
for r in $(seq 1 "$ROUNDS"); do
  pids=(); idx=()
  for i in $(seq 1 "$N"); do
    ( "$B" test "$SPEC" >"scratch_b4/burst/r${r}_i${i}.log" 2>&1; echo $? >"scratch_b4/burst/r${r}_i${i}.rc" ) &
    pids+=($!); idx+=("r${r}_i${i}")
  done
  for p in "${pids[@]}"; do wait "$p"; done
  for id in "${idx[@]}"; do
    rc=$(cat "scratch_b4/burst/${id}.rc" 2>/dev/null)
    total=$((total+1))
    if [ "$rc" = "139" ] || [ "$rc" = "134" ] || [ "$rc" -ge 128 ] 2>/dev/null; then
      if [ "$rc" != "129" ] && [ "$rc" != "143" ]; then
        crash=$((crash+1)); echo "CRASH rc=$rc  $id"
      fi
    fi
  done
  echo "round $r done (avail MB: $(free -m | awk 'NR==2{print $7}'))"
done
echo "=== SUMMARY: crashes=$crash / total=$total (N=$N rounds=$ROUNDS spec=$SPEC) ==="
