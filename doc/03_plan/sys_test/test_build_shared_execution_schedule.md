# Shared build/test scheduler verification

Status: authored; new executable checks have not run.

| Requirement | Evidence required |
|---|---|
| REQ-001 | execution_schedule_spec, scheduler_execution_index_spec, actual shared_async_execution_spec |
| REQ-002 | canonical process owner preserved; real child transport and build receipt regressions |
| REQ-003 | parent-only state mutation review; no concurrent map writers |
| REQ-004 | reservation/reap/retry/cache transitions; actual timeout/cleanup, manifest order and admission failure regressions |
| REQ-005 | exact GNU Phase2 Hello compile/run, descendant CLI and standalone runner build/run; real green/red/empty fixtures |
| REQ-006 | isolated source lineage, verify evidence, reviewed PR merged into release/1.0.0 |

The collection-only async_structured_evidence_spec uses real temporary receipt
files and does not establish child transport or scheduling. It covers transcript
precedence, red/missing/zero evidence, authoritative deadlines, independent
receipt paths and cleanup. The system spec starts actual interpreter children
through run_tests_parallel_with_monitoring, checks returned file order and real
BDD counts, and continues a green sibling after red or empty children.

Require SIMPLE_BINARY and SIMPLE_TEST_BINARY to name the same qualified full
CLI descendant. Missing identity pins must fail, never skip. The bootstrap
compiler itself is not a full interpreter/test CLI. Separate the standalone
runner identity from the CLI that executes child specs.

After meaningful focused checks pass, run the required core/lib/MCP checks and
smokes, runtime env guards, SPipe manual generation/review and repository
verification. Record unexecuted checks explicitly. Do not repeat unchanged green
checks; obey the renewed maximum of three compiler repair cycles.
