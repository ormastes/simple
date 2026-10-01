# Reproduction and prospective comparison commands

Executed source: `e0dd873da1b7828389db4eb60e82972cc8245313`.
Executed runtime tree: `8581b3b54e0cda59ff0c784dec9284ca90d297aa`.
The adjacent `capsule.manifest` records all source/tool hashes. Its built
archive SHA-256 is
`f01799b6c4ba5c8752c73f635242687b141b3f574b5a990a56969c1251816fe5`.
The candidate executable SHA-256 is
`6094dcae291aa984973ccd681f956e67a7a60543ab99f76a29313fbbfdee96d1`.

## Executed baseline commands

Run inside WSL Ubuntu 22.04; Windows invocation was `wsl -e sh -c` with the
following body. `/usr/bin/cc` resolved to GCC 11.4.0. These are historical
commands, not a request to rerun the passing capsule.

```sh
cd /mnt/d/wk-p1-stage4-ast-hir-memory
export GIT_DIR=/mnt/c/Users/ormas/dev/simple/.git/worktrees/wk-p1-stage4-ast-hir-memory
export GIT_COMMON_DIR=/mnt/c/Users/ormas/dev/simple/.git
export GIT_WORK_TREE=/mnt/d/wk-p1-stage4-ast-hir-memory
timeout 120 /usr/bin/time -v \
  sh scripts/check/build-core-c-bootstrap-runtime-capsule.shs \
  --output build/stage4-ast-hir-audit/core-c \
  >build/stage4-ast-hir-audit/capsule-mapped.log \
  2>build/stage4-ast-hir-audit/capsule-mapped.time

STAGE4_PARSE_MEM_MULTI_BINARY=/mnt/c/Users/ormas/dev/simple/bin/release/x86_64-pc-windows-msvc/simple.exe \
STAGE4_PARSE_MEM_MULTI_FILES=4 STAGE4_PARSE_MEM_MULTI_FUNCS_PER_FILE=4 \
STAGE4_PARSE_MEM_MULTI_ROOT=build/stage4-ast-hir-audit/chain \
timeout 30 sh scripts/check/check-stage4-selfhost-parse-memory-multifile.shs \
  >build/stage4-ast-hir-audit/chain.log 2>&1
```

The second command exits before compilation with the retained `chain.log`
provenance error. No tree sampler was used for the executed capsule.

## Prospective compiler comparison — NOT EXECUTED

Prerequisites: two Linux checkouts at recorded baseline/integrated repair SHAs,
each with an admitted source-matched Stage 3 binary and producer-written
`.provenance.env`. Never generate a provenance file merely to pass this gate.
`BASELINE_ROOT`, `REPAIRED_ROOT`, `BASELINE_BIN`, `REPAIRED_BIN`, and
`EVIDENCE_ROOT` below must be absolute paths. Use fresh output paths. The
integrated source SHA is not yet available: #1282 and #1203 remain open and
this audit intentionally applies neither patch.

Run the following once for each `lane` (`baseline`, `repaired`) and `files`
(`4`, `40`), changing those two initial values explicitly. This is a four-case
matrix, not a retry loop. Candidate provenance must match the selected checkout.

```sh
lane=baseline
files=4
case "$lane" in
  baseline) root=$BASELINE_ROOT; candidate=$BASELINE_BIN ;;
  repaired) root=$REPAIRED_ROOT; candidate=$REPAIRED_BIN ;;
  *) exit 2 ;;
esac
cd "$root"
out="$EVIDENCE_ROOT/$lane-$files"
mkdir "$out"
git rev-parse HEAD >"$out/source-revision.txt"
sha256sum "$candidate" "$candidate.provenance.env" \
  scripts/check/check-stage4-selfhost-parse-memory-multifile.shs \
  scripts/check/lib/bootstrap-stage3-rss-evidence.c >"$out/inputs.sha256"
cp "$candidate.provenance.env" "$out/candidate.provenance.env"
clang -O2 -std=gnu11 scripts/check/lib/bootstrap-stage3-rss-evidence.c \
  -o "$out/tree-sampler"
clang --version >"$out/sampler-toolchain.txt"
sha256sum "$out/tree-sampler" >"$out/sampler.sha256"
shell_bin=$(realpath /bin/sh)
shell_sha=$(sha256sum "$shell_bin" | awk '{print $1}')
export STAGE4_PARSE_MEM_MULTI_BINARY="$candidate"
export STAGE4_PARSE_MEM_MULTI_PROVENANCE="$candidate.provenance.env"
export STAGE4_PARSE_MEM_MULTI_FILES="$files"
export STAGE4_PARSE_MEM_MULTI_FUNCS_PER_FILE=20
export STAGE4_PARSE_MEM_MULTI_TIME_MAX_S=120
export STAGE4_PARSE_MEM_MULTI_RSS_MAX_KIB=409600
export STAGE4_PARSE_MEM_MULTI_ROOT="build/stage4-comparison-$lane-$files"
timeout 180 /usr/bin/time -f 'wall_seconds=%e' -o "$out/wall.txt" \
  "$out/tree-sampler" run --interval-ms 10 --raw "$out/tree.raw" \
  --sha256 "$shell_sha" --run-id "$lane-$files" -- "$shell_bin" \
  scripts/check/check-stage4-selfhost-parse-memory-multifile.shs \
  >"$out/gate.log" 2>"$out/gate.err"
rc=$?
printf 'exit_code=%s\n' "$rc" >"$out/exit.txt"
[ "$rc" -eq 0 ] || exit "$rc"
"$out/tree-sampler" validate --run-id "$lane-$files" "$out/tree.raw"
awk '$1 == "sample" {
  tick=""; rss=0
  for (i=2; i<=NF; i++) {
    split($i, field, "=")
    if (field[1] == "mono_ns") tick=field[2]
    if (field[1] == "vmrss_kb") rss=field[2]+0
  }
  total[tick]+=rss
} END {
  for (tick in total) if (total[tick] > peak) peak=total[tick]
  if (peak <= 0) exit 2
  printf "sampled_tree_peak_kib=%.0f\n", peak
}' "$out/tree.raw" >"$out/tree-peak.txt"
```

The sampler pins/hashes the measured **shell**, whose descendants include the
gate and compiler. The gate independently verifies compiler/source provenance;
`inputs.sha256` records the candidate. Compare the same wrapper/process scope
on both revisions. Sum RSS only within one `mono_ns` snapshot, never sum each
process's individual lifetime high-water mark. Shared resident pages can be
counted in multiple process RSS values; keep that accounting identical on both
sides. A 10-ms sampled peak can miss shorter-lived peaks.

Retained-HIR adjacent gate (only available after incorporating #1282):

```sh
SIMPLE_BIN="$candidate" STAGE3_HIR_RSS_MAX_ELAPSED_S=120 \
STAGE3_HIR_RSS_MAX_RSS_KIB=1048576 \
sh scripts/check/check-stage3-hir-retained-parser-rss.shs \
  >"$out/retained-hir.log" 2>&1
```

That gate needs a self-hosted runner supporting `run`, not a minimal Stage 3
CLI that only supports `native-build`. Rebuild/admit the correct runner before
using it. It tests two and 16 retained modules in separate processes; retain
its printed summary. Its internal temporary files are removed by the wrapper,
so obtain raw process-tree and leak evidence separately before admission.

The source runtime controls are
`src/runtime/test/rt_transient_heap_scope_selfcheck.c` and
`src/runtime/test/rt_transient_heap_thread_affinity_selfcheck.c`, invoked by the
capsule gate. Their existing checks do not include a general leak detector or
pre-cleanup descendant-survivor assertion. Those conditions remain BLOCKED;
sampler cleanup must not be treated as proof that the workload exited cleanly.
Do not mark the memory bug fixed from this recipe alone.
