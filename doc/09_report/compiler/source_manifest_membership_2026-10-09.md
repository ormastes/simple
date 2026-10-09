# Bounded paired source-membership diagnostic

## Change and admission status

STATUS: WARN - source candidate, not qualified for landing or deployment.

Source authority used to allocate a hash table for every global inventory entry
even for a one-file selection. The new pure-Simple helper uses canonical UTF-8
identity binary search for at most 32 selected rows and at most 1/16 of the
inventory. It confirms the complete path/digest/size row; synthetic unsorted,
duplicate, or delimiter-containing identities retain exact linear fallback.
Large selections retain the original hash-table algorithm. No mutable shared
state, persistent cache, digest bypass, or authority widening is introduced.
Manifest hash/count, inventory digest/generation and publication remain checked
by the existing caller. This implements only a source-authority substep of TLDR
optimization, not complete header-only compilation or target-scoped inventory.

The focused SSpec passed 1 example with 32 real membership checks, including
thresholds, malformed/missing rows, differing content/size, ordering, duplicates
and retained caller inputs. The delimiter regression failed before the complete
row fallback fix and passed afterward. This is diagnostic seed evidence.

Broader source_authority_spec.spl returned 2 passed / 2 failed for both candidate
and original caller. Counts alone do not establish identical failing assertions.
Reason-printing harnesses then failed before main on both versions with E1002:
transient_array_scope_begin_v1 not found. The import is in inventory_scratch.spl;
the compiler dependency is absent from the sparse diagnostic checkout. Preserve
this as an unresolved integration blocker; do not label those failures unrelated.
The candidate caller was restored byte-for-byte after baseline comparison.

Remaining admission work: execute broader source authority integration in a
complete isolated checkout, then qualify with an admitted pure-Simple binary.
No optimizer-app run, core/MCP native smoke, warm/cold native object build, or
0.1-second compilation target has been qualified. Do not replace production
tooling with the diagnostic seed. Cold whole-family inventory scans remain a
separate bottleneck; narrowing global CURRENT to a selected target is unsafe.

## Reproduction and retained evidence

Frozen measured harnesses and raw/summary/provenance JSON are under
test/05_perf/compiler/source_manifest_membership/evidence_20261009/. They are
diagnostic programs, not auto-discovered SSpec examples. They deliberately
contain frozen baseline/candidate code for reproducibility, not reusable runtime
implementations. Run each with the pinned producer using `run <harness.spl>` and
SIMPLE_EXECUTION_MODE=interpret. Each must exit 0 and print exactly ten expected
booleans. Source and harness hashes are recorded in provenance.json.

Focused spec: with SIMPLE_TEST_RUNNER_RUST=1, SIMPLE_EXECUTION_MODE=interpreter,
and SIMPLE_LIB=src, run the pinned producer with
`test test/01_unit/app/compiler_entrypoint/source_manifest_membership_spec.spl --mode=interpreter --no-unstable --format json`.
Keep the standalone interpret selector distinct from the test runner selector.

## Measurements

All 16 measured processes exited 0 and printed their expected boolean exactly ten times. Missing-entry cases returned false; other cases returned true. Two complete pairs per case, alternating candidate/baseline then baseline/candidate. No production source or Git index changes.

Pinned interpreter producer: `15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb`, path and source/harness SHA-256 hashes in `provenance.json`. Explicit `SIMPLE_EXECUTION_MODE=interpret`; this is Rust bootstrap-seed diagnostic evidence, not self-hosted qualification.

Candidate embeds the current production membership helper, including its complete-row linear fallback, and exact comparator extracted from production source. Baseline embeds the historical hash-set algorithm. Each process constructs its fixture, then makes ten calls. Entries use the same constant `digest` and length 128 in both variants; unlike the historical cohort, this matrix uses a shorter digest string. Historical timing is not directly comparable.

| Case | Baseline p50 ms | Candidate p50 ms | Baseline p95 ms | Candidate p95 ms | Baseline peak B | Candidate peak B |
|---|---:|---:|---:|---:|---:|---:|
| Selected 1 / 20000 | 5012.77 | 4435.30 | 5146.94 | 4813.73 | 111632384 | 112168960 |
| Missing 1 / 20000 | 8678.21 | 7915.76 | 8917.65 | 8085.99 | 111362048 | 101015552 |
| Selected 33 / 20000 | 6710.45 | 6739.58 | 7739.19 | 7187.50 | 111370240 | 103665664 |
| Selected 1 / 8 | 1249.55 | 1171.91 | 1776.90 | 1827.66 | 18063360 | 19169280 |

Selected-one median improved 11.52%, with peak memory increasing 0.48%. Missing-one median improved 8.79%. The batch-path median regressed 0.43%. Small-inventory median improved 6.21%, but observed p95 increased 2.86% and peak memory increased 6.12%. These tiny cohorts on a concurrently active host cannot establish small regression significance or reliable tail guarantees. The missing-case fallback still scans and formats all rows; these observations do not change that complexity.

Wall times include interpreter startup, parsing, fixture construction, assertion/output overhead and Windows process observation. p50 is the two-sample median (average); nearest-rank p95 is the maximum. Peak RSS is the maximum observed `PeakWorkingSet64`, sampled every 25 ms. Each hidden process had a 30-second guard; no timeouts occurred.

The first Windows PowerShell measurement lost its exit-code handle despite ten correct outputs. Its raw record is preserved under `instrumentation-first-attempt/raw.json` and the sample-1 stdout/stderr remain in this directory. It is excluded from summaries. Retaining the process handle fixed instrumentation; only two subsequent pairs were run per case, respecting the three-attempt ceiling. An earlier PowerShell execution-policy refusal launched no benchmark process.

Tracked evidence contains raw.json (including stdout/stderr), summary.json,
provenance.json and eight measured .spl harnesses. The local process-measurement
script and excluded instrumentation attempt remain in the diagnostic build
directory. No broader builds or production qualification claims.

The p95 time ratio plus peak-RSS ratio is approximately 1.940 for selected-one,
1.814 for missing-one, 1.859 for batch, and 2.090 for small-inventory. The latter
does not meet the joint optimization acceptance rule; the tiny noisy cohort
cannot support an across-the-board performance PASS. Startup, steady-state and
native-build costs are not separated here. Further qualification must measure
them separately before asserting a production improvement.
