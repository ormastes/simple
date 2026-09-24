# Stage 3 cannot start: the canonical Stage-3 step passes no package-index authority and no cold-init
## Closed 2026-09-16 — ...nus the planner-admission receipt. ## Fix direction (not applied by this lane) Add `SIMPLE

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

- Status: OPEN (2026-09-13)
- Area: bootstrap / 80.driver source pipeline
- Found by: BOOT-14 (first Stage-3 run ever reached in this lane series)

## Symptom (verbatim, run `s3a`)

`build/bootstrap-boot14a/logs/aarch64-unknown-linux-gnu/stage3-native-build.s3a.log`:

```
[BOOTSTRAP-PHASE] +0ms compile:start
[build] phase=load_sources state=running unit_kind=files ... task_total=6 elapsed_ms=14 dt_ms=0 current=starting
[BOOTSTRAP-PHASE] +14ms phase1:load_sources:start
[ERROR] phase 1 FAILED
[build] phase=load_sources state=failed unit_kind=files ... cached=0 failed=1 task_done=0 task_total=6 elapsed_ms=20 dt_ms=6 current=failed
error: focused native-build: persistent package index admission failed: scv-authority-missing; run explicit cold initialization with SIMPLE_PACKAGE_INDEX_COLD_INIT=1
```

Wall time to failure: 3 s. Nothing is compiled; phase 1 never loads a source.

## Cause — measured, not guessed

`src/compiler/80.driver/driver_source_pipeline_loading.spl:202-227` fail-closes when
`SIMPLE_PACKAGE_INDEX_COLD_INIT != 1` and `package_index_route_current_v1(...)` finds no SCV
authority (`SIMPLE_SCV_SNAPSHOT_ROOT` / `SIMPLE_SCV_REVISION_ID` / `SIMPLE_SCV_TREE_ID` /
`SIMPLE_SCV_INVENTORY_DIGEST` all empty) -> `route.valid == false`, reason `scv-authority-missing`.

The Stage-3 child runs under `env -i` (`bootstrap_stage3_run_transcribed`), so it sees ONLY the
variables the step lists. Grepped across the three callers that drive a Stage-3 native build:

| caller | sets `SIMPLE_PACKAGE_INDEX_COLD_INIT` | sets any `SIMPLE_SCV_*` |
|---|---|---|
| `scripts/bootstrap/bootstrap-from-scratch.sh:3344-3401` (Stage 3) | **no** | **no** |
| `scripts/bootstrap/resume-stage3-from-admitted.sh:612-635` | **no** | **no** |
| `scripts/check/lib/bootstrap-stage3-candidate-builder.shs:310-335` | **no** | **no** |
| `scripts/check/check-bootstrap-stage2-struct-receiver.shs:147` (positional Stage-3 route probe) | **yes, `=1`** | no |

So the only Stage-3-SHAPED invocation that has ever run to completion in this tree is the receiver
probe, and it works *because* it sets the variable. The three real Stage-3 steps do not, and cannot
get past phase 1. This had never surfaced because Stage 2 has not been admitted in this lane series,
so no run ever reached Stage 3 (BOOT-12's receipt: "Stage 3 / 4: NOT RUN").

## One-variable discriminator

Identical command, identical env, identical candidate
(`aad572408ec06e53c3b064ab3e2a8ffe86e2663e183e0e0a28288eaf177f2e85`, 152287536 B, built by this
lane's `--full-bootstrap --stop-after-stage2` at `bcb311feff3`), one variable added:

| run | added | result |
|---|---|---|
| `s3a` | — | `phase 1 FAILED` / `scv-authority-missing` at +20 ms |
| `s3b` | `SIMPLE_PACKAGE_INDEX_COLD_INIT=1` | phase 1 passes; phase 2 parses (`phase2:surface:file:parse-start path=src/std/...`) and the build proceeds |

Repro: `$S/boot14/stage3.sh s3a` vs `STAGE3_COLD_INIT=1 $S/boot14/stage3.sh s3b`, where that script
replicates `bootstrap-from-scratch.sh:3344-3401` argv-for-argv and env-for-env through the repo's own
`bootstrap_stage3_run_transcribed`, minus the planner-admission receipt.

## Fix direction (not applied by this lane)

Add `SIMPLE_PACKAGE_INDEX_COLD_INIT=1` to the Stage-3 step in all three callers above, in BOTH the
`bootstrap_stage3_args_sha256` vector and the transcribed invocation (they are deliberately
word-split from one list so they cannot diverge) — exactly as the receiver probe already does for the
same route. A fresh per-stage `stage3-native-cache` has no persistent index to reuse, so cold init is
the correct route, not a relaxation.

**This changes the Stage-3 args hash, which admission receipts bind to**, so it belongs to whoever
owns the admission chain, not to a diagnostic lane. Recorded here with the measurement instead of
applied.

