# Pre-existing failures in specs consolidated by PR #7931

Status: open. Found during release health check 2026-11-09 (base release/1.0.0).

PR #7931 merged `test/unit/app/**` specs into `test/01_unit/app/**`. Each failing spec was
run with the seed (`C:/dev/simple/bin/simple.exe test <spec>`, cwd = worktree) at three
points: OLD = #7931 parent `98f1045c5f9` `test/unit/...`, P01 = parent `test/01_unit/...`,
NEW = release/1.0.0. The failures below already failed at OLD or P01, so they are NOT
caused by the move. Move regressions were fixed separately (see PR body of
work/move7931-regressions).

| spec (test/01_unit/app/) | NEW | failing scenario(s) | already failed at | first error |
|---|---|---|---|---|
| browser/browser_render_lane_spec | 11/13 | inline style= ignored; author `a{color}` override | OLD | assertion |
| doc_coverage/sdoctest_coverage_spec | 7/8 | finds at least one markdown code block | P01 | assertion |
| serial_mcp/serial_mcp_spec | 0/1 | whole file | OLD | parse error `src/lib/nogc_sync_mut/mcp_sdk/server/app.spl`: expected expression, found Dedent |
| sj/forbidden_verbs_spec | 23/29 | 6 protected-ref/raw-mutation scenarios | P01 | assertion |
| test_daemon/test_daemon_mcdc_request_spec | 5/8 | MC/DC on/off/refuse | OLD | assertion |
| test_runner/args_spec | 102/104 | defaults timeout to 120; parses --format json | OLD | assertion |
| test_runner/types_spec | 34/36 | creates Text variant; distinguishes Text from Doc | OLD, P01 | unknown variant `Text` on enum OutputFormat |
| tooling/compile_commands_spec | 40/41 | extracts source from args[2] | OLD | assertion |
| tooling/test_runner_simple_spec | 66/74 | recursion-guard / docgen scenarios | OLD or P01 | `generate_spipe_docs_for_results` not found, etc. |
| ui/backend_matrix_spec | 1/9 | widget matrix renders | OLD, P01 | assertion |
| ui/session_spec | 20/23 | tree theme isolation; changelog | OLD, P01 | assertion |
| ui/wm_runtime_bridge_spec | 5/6 | non-left/non-down pointer ignored | OLD | assertion |
| ui/ws_handler_spec | 12/14 | RFC accept hash; bearer from query | OLD, P01 | accept hash `wrN6Tyz...` vs `s3pPLMBiTxaQ9kYGzzhZRbK+xOo=` (looks like digest bytes re-encoded as UTF-8 before base64) |
| slang_pack/main_spec | (see PR) | exits 0 on valid tiny safetensors | OLD | needs fixture absent in unit lane |

Next: split each row into its own bug when a fix lane picks it up.
