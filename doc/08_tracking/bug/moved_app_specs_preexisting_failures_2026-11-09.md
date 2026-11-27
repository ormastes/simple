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

## Progress 2026-11-27 (Windows host, W2-3)

Fixed and verified in W2-3:
- `test/01_unit/app/ui/session_spec.spl`: 23/23 PASS (`src/lib/common/ui/wm_chrome_theme.spl` exports added; `src/lib/nogc_sync_mut/ui/session.spl` `UISession.update_tree` / `update_surface_tree` fall back to `diff_trees(...)` global store; `session_spec.spl` updated for non-alias `glass_dark` per `23c09d490df`).
- `test/01_unit/app/ui/backend_matrix_spec.spl`: 10/10 PASS (`src/app/ui.render/_TuiWidgets/extended_widgets.spl` adds `tui_renders_own_children` including `"dropdown"`, `"table"`, `"radio"`, etc. so `render_tui_tree` does not re-render child widgets over self-rendering widgets; `backend_matrix_spec.spl` uses `480x40` TUI viewport matching `nav_panel width: 240` and adds a radio group marker test).
- Re-verified adjacent UI/TUI specs with zero regressions: `ui/ws_handler_spec.spl` 13/13 PASS, `ui/tui_cli_wiring_spec.spl` 7/7 PASS, `test/03_system/gui/tui_screen_spec.spl` 11/11 PASS, `backend_matrix_{web,tauri,electron}_spec.spl` 1/1 PASS each.
- Remaining outside W2-3 / host scope: `browser/browser_render_lane_spec` (in excluded `simple_web_html_layout_renderer.spl`), `backend_matrix_browser_spec` (1/2 fails Engine2D GPU backend expectation software vs cuda/rocm/opencl), and `slang_pack/main_spec` (fixture). Bug remains open.

## Progress 2026-11-27 (Windows host, W4-7)

- Verified PASS (`wa3_shared_bin/simple.exe --mode=interpreter`, `SIMPLE_LIB=src`):
  - `test/01_unit/app/browser/browser_render_lane_spec.spl` (12/12 PASS)
  - `test/01_unit/app/ui/backend_matrix_spec.spl` (10/10 PASS)
  - `test/01_unit/app/ui/session_spec.spl` (23/23 PASS)
  - `test/01_unit/app/ui/ws_handler_spec.spl` (13/13 PASS)
  - `test/01_unit/app/ui/wm_runtime_bridge_spec.spl` (6/6 PASS)
  - `test/01_unit/app/serial_mcp/serial_mcp_spec.spl` (17/17 PASS)
  - `test/01_unit/app/sj/forbidden_verbs_spec.spl` (28/28 PASS)
  - `test/01_unit/app/test_daemon/test_daemon_mcdc_request_spec.spl` (8/8 PASS)
  - `test/01_unit/app/test_runner/args_spec.spl` (103/103 PASS)
  - `test/01_unit/app/test_runner/types_spec.spl` (36/36 PASS)
  - `test/01_unit/app/tooling/compile_commands_spec.spl` (41/41 PASS)
  - `test/01_unit/app/slang_pack/main_spec.spl` (5/5 PASS; fixed the malformed-safetensors test to actually write 12 invalid bytes `[4u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0x42u8, 0x41u8, 0x44u8, 0x21u8]` to `/tmp/svllm_a2_cli_bad.safetensors` so it hits `parse_safetensors_header` error `malformed safetensors` instead of missing-file/short-read, and clean up `/tmp/svllm_a2_cli_*` scratch artifacts)
- Remaining FAILs (honest environment / hardware / sparse-checkout constraints; row stays `open`):
  - `test/01_unit/app/ui/backend_matrix_browser_spec.spl` (1/2 PASS, 1 FAIL): `keeps canonical Engine2D backend selection visible through the browser adapter` expects `cuda`/`rocm`/`opencl`/`vulkan` from `BrowserBackend.create`, but `resolve_gpu_backend` falls back to `"software"` on hosts without GPU hardware/drivers (`simd_cpu` -> `cpu_simd` passes).
  - `test/01_unit/app/tooling/test_runner_simple_spec.spl` (68/74 PASS, 6 FAIL): only `Simple Test Runner Recursion Guard` fails because it reads `src/compiler_rust/**`, excluded from this slim sparse checkout cone.
  - `test/01_unit/app/doc_coverage/sdoctest_coverage_spec.spl` (7/8 PASS, 1 FAIL): `finds at least one markdown code block in this repository` scans `./README*.md`, `doc/*.md`, and `doc/07_guide/**/*.md`, excluded from this slim sparse checkout cone.
