<!-- codex-design -->
# Pure-Simple tool and infrastructure hardening design

## Interfaces and flow

- The implemented sequential interpreter `simple test --assert-ran` paths use a private
  result file containing canonical `simple-bdd-v1` counts. Missing, malformed,
  empty, pending-only, or stdout-forged evidence fails closed. Other execution
  modes fail closed under `--assert-ran` until they supply the same evidence.
- `simple lint` calls `run_lint_file` directly. Human and JSONL output share
  the same findings and exit status. `--fix-dry-run` is an independent mode;
  fixes use `file_atomic_write`, report structured success/failure in JSON, and
  return nonzero on write failure.
- `simple duplicate-check` uses native directory/file owners, normalizes only
  the terminal split artifact, and canonicalizes occurrence sets before totals.
- `check-bootstrap-essential-tools-smoke.shs` proves one real pass/failure for
  each essential tool and rejects fallback/help/zero-file false greens.

## Error handling

Every qualification child call is deadline-bound. Child exit is preserved before parsing
presentation text. Missing files count as failed lint inputs. Unsupported JSON
repository modes return usage error; unauthenticated assert-ran modes fail
closed and cannot qualify a release.
Incremental object-cache publication accepts a racing destination only when
the completed bytes match. Lint atomic replacement reports failure and never
claims a mutation succeeded when it did not.

## Observability and budgets

Verbose native builds expose dirty/cached counts and periodic compile progress.
Verification records command, binary hash/provenance, exit, elapsed time, and
max RSS. Warm focused tool p95, single-test p95, runner RSS, MCP/LSP latency/RSS,
and cold/warm/invalidated cache equivalence use the selected NFR thresholds.

There is no TUI/GUI surface; UI design is N/A.

## Requirement-to-implementation mapping

| Requirement | Primary owner(s) |
|---|---|
| REQ-001 | `scripts/setup/setup.shs`, production wrapper admission helpers |
| REQ-002 | `scripts/bootstrap/bootstrap-from-scratch.sh`, `scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs` |
| REQ-003 | `src/app/test_runner_new/test_runner_single.spl`, `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl` |
| REQ-004 | `src/lib/nogc_sync_mut/spec.spl`, test-runner execution owners |
| REQ-005 | `src/app/test_runner_new/test_runner_client.spl` |
| REQ-006 | `src/lib/nogc_sync_mut/test_runner/test_runner_types.spl`, `test_executor_parsing.spl` |
| REQ-007 | `src/compiler/90.tools/duplicate_check/` native file owners |
| REQ-008 | `test/05_perf/duplicate_check_benchmark_spec.spl` |
| REQ-009 | `src/compiler/90.tools/lint/` canonical parser/linter |
| REQ-010 | `src/app/io/cli_lint_commands.spl`, `_LintMain/entry_and_fixes.spl` |
| REQ-011 | `src/app/cli/dispatch.spl` canonical command table |
| REQ-012 | `bin/simple_mcp_server`, `bin/simple_lsp_mcp_server`, native protocol/hash admission helpers |
| REQ-013 | `src/app/test_daemon/`, shared daemon binary/cache owners |
| REQ-014 | checker flag parsing and `src/app/gen_lean/main.spl` bounded dispatch |
| REQ-015 | system spec/manual, this mapping, and `doc/07_guide/tooling/pure_simple_tooling.md` |
