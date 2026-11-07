# Baremetal boolean consumer reproduction — 2026-11-07

**Not fixed in release `6b9613f2d27594f25da3443c4e3c30ad473cafb3`.** This test-only change adds a runnable C ABI reproducer and adjacent prevention cases; it does not land the candidate production repair or close #7319.

| Exact source | Owner | Assertions | Failed | Exit |
|---|---|---:|---:|---:|
| release `6b9613f2d27594f25da3443c4e3c30ad473cafb3` | x86_64 | 190 | 25 | 1 |
| same release | ARM64 | 190 | 25 | 1 |
| candidate #7319 `41fb5530ad3d49924f560a86abe29544a42cb4f5` | x86_64 | 190 | 0 | 0 |
| same candidate | ARM64 | 190 | 0 | 0 |

The first assertion proves `rt_not(19)` incorrectly returns 19 instead of 11 on release. Other failures include `rt_to_bool(11)`, boolean recognition and false-valued logical operands. The identical 190-assertion fixture passes with each candidate's complete production object. Both objects are compiled for their actual architecture and linked into freestanding static ELFs; QEMU user mode executes those ELFs. Production definitions are not extracted or replaced.

Original/adjacent case details and commands: [fixture README](../../test/fixtures/runtime/baremetal_tagged_bool_repro/README.md). Full failure output, compile warnings, source/binary/tool digests and exit receipts: [.spipe evidence](../../.spipe/bug_repro_review_20261107/). The original x86 run preceded adding tool digests to the wrapper; its receipt binds owner, fixture, startup, object and executable. ARM64 has an existing unrelated negative-shift compile warning; it does not execute that function. The first x86 harness link attempt collided with production `_start`; the fixture now has its own `repro_start` and changes no production symbol.

## Admission boundary

This is C ABI integration evidence, not a Simple compiler-generated caller, device boot, end-to-end fix admission, or 100% owner branch coverage. Heap conversion branches are untested. The original #7319 preconditions remain outstanding. No green compiler/lib/MCP result or bug closure is inferred from these passes. #7294 and #7337 exhausted-budget failures were not rerun. No new bootstrap was attempted.

Astra reviews the final test/evidence diff before it lands. Token usage and comparable-cohort usage are unavailable; no invented usage ratio or fixed-bug receipt is recorded.

## Astra review and provenance correction

Astra confirmed the oracle, case count, real-owner linkage and scope, and requested one fix: the default runner must archive HEAD rather than compile potentially dirty working-tree headers. The final runner now always archives the exact revision and records its own hash, the full source archive and lld identity. Original run artifacts are retained without rewriting them as post-review executions; the prior wrapper is preserved as `runner_before_provenance_fix.shs.txt` (used for ARM64 release and both candidate runs). The earlier x86 wrapper identity was not recorded, as noted above. Production input files were unchanged in this isolated worktree. These metadata changes do not claim a new compiler or system acceptance run.
