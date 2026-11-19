# Profile HIR workers re-parse the whole closure and exceed the 1800 s internal timeout

- Status: open
- Severity: P1 (perf). Blocks Stage 2 admission: `stage2-compiler-tests` rows `compiler_cli_build` / `test_runner_build` fail with `HIR aggregate failure`.
- Found: 2026-11-20, ubuntu-p2 (WSL2, 64 GB) phase 2 at `4ea6d974967`
- Component: profile HIR shard workers (`src/app/cli/worker_hir_owner_v1.spl`, `src/app/cli/native_build_main.spl`), bootstrap verify timeout policy
- Related: `hir_worker_deadline_retirement_reason_empty_2026-11-20.md` (PR #10526 named the deadline; this record tracks the cause)

## Observation
`compiler_cli_build`: coordinator loads 7005 files in ~150 s, then launches 3 HIR workers (estimate 9 GB each). Each worker repeats the whole frontend prologue (`phase2:surface` over the full closure) and never claims a module before the row's `native_internal_timeout_seconds=1800` deadline. Row elapsed 1832 s, measured worker peak commit 10,029,610 kB (static estimate 9,000,000 kB). All owners end BLOCKED, `claimed=0`.

## Needed
- Workers must reuse the coordinator's parsed closure / surface (or a published summary) instead of re-parsing ~7005 files each, OR
- the verify timeout for these rows must be fitted to the measured prologue (stopgap only; record the measured cost).
- The 9 GB worker estimate is ~11% under the measured 10 GB commit.
- Reap should report `TIMEOUT`, not `BLOCKED`, when an owner retired on its own deadline.

## Repro
`bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 --mode=dynload --jobs=12 --no-mcp`, `COMPILER_BUILD_TIMEOUT_SECONDS=900`, `SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=50331648`. Wall 8636 s, peak 33.5 GB.
