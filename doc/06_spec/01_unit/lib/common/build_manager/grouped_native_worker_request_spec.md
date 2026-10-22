# Grouped worker request defining owner

The executable specification is `test/01_unit/lib/common/build_manager/grouped_native_worker_request_spec.spl`. Its four shared checks also run from `test/fixtures/bootstrap/grouped_native_request/main.spl` without importing the worker executable or test runner.

| Requirement | Actual assertion |
|---|---|
| REQ-HIR-GROUPED-REQUEST-001 | Compare encoded bytes with independently written canonical payload and check all14 decoded fields. |
| REQ-HIR-GROUPED-REQUEST-002 | Reject65537-byte input, wrong header, trailing data and a leading-zero thread count. |
| REQ-HIR-GROUPED-REQUEST-003 | Fresh requests reject relative paths, invalid digests, foreign entry/result roots, overlapping output, unsupported backend and NUL target. |
| REQ-HIR-GROUPED-REQUEST-004 | Accept threads1/256 and timeout0/86400000; reject adjacent out-of-range values. |

The existing `test/01_unit/app/bootstrap_builder/grouped_native_worker_spec.spl` continues to import the historical worker facade, covering its preserved public request exports. There is only one struct definition, at the new contract owner.

Native probe success requires exit0 and `GROUPED_NATIVE_REQUEST_PASS cases=4` followed by a newline. Specification and native probe are UNRUN at authoring. Static body identity is not runtime ABI or performance evidence. The separate failed `grouped_native_run.spl` object build must be measured with the admitted70194 producer and its unchanged300-second task deadline; compare actual closure, phase timing and peak RSS with the retained baseline. Core/MCP smoke checks remain UNRUN until a suitable qualified runner is available.

## Recorded evidence, 2026-10-18

Feature source commit: `68e74662c5f37d2aee0e619daa59acd5a5f872cb`. The standalone companion object compiled with admitted producer70194 in 7430 ms; all ten modules passed HIR, MIR and native compilation. Object SHA256: `29644e6a3ebef2df3bb56a9cc03878b1b187b8f1881fc61c7d4b95983a88dc48`. This is compilation evidence only: the four shared assertion cases and SSpec execution remain UNRUN. Three bounded manual-link setup packets stopped at peer admission before compilation/linking/runtime; no assertions were executed.

The separate parent target completed all168 HIR modules by60943 ms within its300-second deadline, then failed MIR with20 errors across six families and produced no object. See `doc/08_tracking/bug/grouped_native_request_import_timeout_2026-10-18.md` for exact source epochs and terminal assessments. Core/MCP and full Phase3 qualification remain UNRUN; no performance percentile or memory improvement claim is made.
