# Target 6 warm inventory batch reducer (2026-09-28)

The old warm path called `compile_source_inventory_apply_event_v1` against the
whole inventory for every observed event. That repeatedly searched and copied
the complete inventory for a batch. The new path uses the serial reducer on
each event's one identity, retains one indexed working set, and sorts the
survivors once. One-event refreshes keep the existing lower-allocation path.
No persistence format or public API changed.

## Paired native workload

The baseline and candidate were built on the same aarch64 Linux host from the
same `test/05_perf/scv/warm_inventory_batch_workload.spl` by the admitted
pure-Simple Stage2 compiler SHA-256
`d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c`.
Both builds used `SIMPLE_NO_STUB_FALLBACK=1`,
`SIMPLE_SCV_FREEZE_FALLBACK=1`, the core-C runtime, and an entry closure.
The fixture seeds 1,200 sources and applies 60 tracked edits in one warm
publication. Each binary ran 30 separate processes; `warm_ns` brackets the
warm batch and publication, and `/usr/bin/time` recorded peak process RSS.
Samples and build logs are under `build/mini_builds/target56_warm_batch_*`.

| Metric | Baseline | Candidate |
|---|---:|---:|
| Binary SHA-256 | `cedac6ebfb8c99214c7c8e72cf29987fc7ac056114e4be41aa4695a1454bd7b3` | `41034fd9212203b4529f8d0c2a6236480f3a5e025e7e723065851aecd2dabac9` |
| Native binary bytes | 143,040 | 146,000 |
| Warm p50 | 103.43 ms | 55.33 ms |
| Warm p95 | 131.89 ms | 101.47 ms |
| Peak process RSS | 41,816 KiB | 40,840 KiB |

The p95 time ratio is 0.769405 and peak-RSS ratio is 0.976660; their sum is
1.746065. Both measured metrics improve. The 2,960-byte worker binary growth
is separate from the Target 5 release-small hello size gate. Steady RSS was
not sampled, and this synthetic fixture is not the production cold/warm/edit/
SCC/variant cohort or a release qualification.

The isolated worktree has no full pure-Simple `bin/simple` launcher, and its
admitted Stage2 binary is compiler-only, so the source optimizer CLI and the
required full core/MCP smoke scripts cannot run on this authority. The MIR
optimizer plugin and legacy source scanner were inspected; neither owns this
SCV reducer. The focused no-stub native builds provide the local evidence
above while Stage4/full-CLI qualification remains open.

## Correctness

`test/fixtures/compiler/scv_warm_batch_native_probe.spl` passed under the
same no-stub native producer. It compares encoded output with the original
serial reducer across a no-op, modification, deletion, recreation, and absent
deletion; then it proves that a later invalid event rejects the whole batch
without moving the published pointer. The corresponding SPipe unit spec ran
through the bootstrap interpreter as a diagnostic and reported `20 passed, 0
failed`. The full current-source test worker remains unavailable because its
optional-runtime link closure is unresolved.
