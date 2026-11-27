# In-process LSP MCP document symbols exceed Linux resource targets

Status: partially fixed 2026-11-24. Per-symbol re-reads and re-parses were already removed by 70d34196da3 and 8a04b71ff1f (one parse, facts hoisted). This change adds a per-request read memo for the in-process lsp_symbols path (source_reader begin_disk). The p95 and RSS targets are NOT re-measured: no idle host or native build was available. Keep open until remeasured.

The Phase 2 whole-program Linux LSP MCP executable built from `70d34196da3`
(SHA-256 `f029fae5735030fb4af98f3475fd9c454536f243a9522cde2cd547f039295d16`)
returned correct visibility-filtered document symbols but exceeded the
request-latency and RSS thresholds in
`scripts/check/check-mcp-lsp-nfr-evidence.shs`.

Start the native server with `SIMPLE_BINARY` pointing at a nonexistent file,
complete the MCP stdio handshake, and request `lsp_symbols` on
`src/app/simple_lsp_mcp/main.spl` once with `visibility: "all"` to verify
`SERVER_NAME`. On the same connection, send 20 successive requests with
`visibility: "public"` and verify that each returns a populated hidden summary.
Measure each request from send to response with a monotonic clock. Measure
peak child RSS after closing stdin and reaping the server.

All 20 public-view calls returned correct results. Startup was 4.7 ms.
Request p95 was 704.6 ms against a 200 ms target. Peak child RSS was
1,797,420 KiB against a 1,048,576 KiB target. These results were collected on a
Linux x86-64 host with concurrent bootstrap workloads and full swap. Repeat the
same sequence on an idle host to distinguish resource contention from the
request's retained allocations.

Inspect repeated file and boundary lookups in the visibility classification
path, and measure RSS after successive requests in the same server process.
Preserve visibility filtering and the hidden summary while reducing p95 below
200 ms and peak RSS below 1 GiB.

## Root Causes & Fixes (2026-11-24, branch `work/mp4-lsp-symbols-perf`)

1. **Multi-pass / quadratic JSON escaping (`json_helpers.spl`, `_QueryVisibility/symbol_resolution.spl`, `query_commands.spl`)**:
   - Replaced the 5-pass `.replace()` chain in `src/app/simple_lsp_mcp/json_helpers.spl` and `_QueryVisibility`'s import of `common.text_advanced.escape_json` (`s.chars()` + `+=` concatenation) with single-scan byte slice-chunk `[text].join("")` implementations featuring a zero-allocation fast-path when no byte is `< 0x20`, `"` (`0x22`), or `\` (`0x5c`).
2. **O(N^2) JSON field/ID extraction (`json_helpers.spl`, `tools.spl`)**:
   - Replaced character-slice `_char_at` / `_slice_text` loops in `_find_json_value_start`, `extract_field`, and `extract_id`, and multi-pass `arg_int_field` / `lsp_parse_diag_line` / `_detect_tool_name_with_params` lookups, with single-pass `byte_len()` / `byte_at()` / `substring()` scanners.
3. **Repeated disk reads, file-content existence probes, and duplicate boundary walks (`_QueryVisibility/source_reader.spl`, `feature_visibility.spl`, `visibility_state.spl`, `tools.spl`)**:
   - Fixed `query_visibility_source_exists_v1` in non-overlay mode to call `query_file_exists` instead of reading whole file contents through `query_file_read_rich`.
   - Added request-scoped disk memoization (`query_visibility_source_disk_begin_v1` / `query_visibility_source_disk_finish_v1`) cleared on request exit so target files, `__init__.spl`, and feature manifests are stat/read at most once per request without retaining heap data across requests, and added O(1) Dict path lookup (`_VIS_SOURCE_PATH_IDX`) in active overlay reader mode.
   - Reused `query_visibility_last_ok()` / `query_visibility_last_has_boundary()` via `lsp_mcp_view_line_for_boundary` in `tools.spl` so `lsp_mcp_view_line_for_file` does not repeat the ancestor `__init__.spl` directory walk.
4. **Hot-loop splits and per-symbol allocation (`_QueryVisibility/symbol_resolution.spl`, `symbol_views.spl`, `query_commands.spl`)**:
   - Eliminated `text_chars` (`split("")`) and `.split(...)` loops in `declaration_token`, `extract_symbol_at`, `token_name_at`, `layer_dir_basename_is_layer`, and `scan_semantic_tokens`.
   - Added `FileBoundaryJsonCache` + `symbol_visibility_json_fast` + `_qv_symbol_admits_fast`, fast-paths in `strip_visibility_prefix`, `declared_visibility_from_line`, `domain_block_kind`, `_parse_decl_kind_and_name`, and `repo_relative_path`, and renamed private `is_ident_byte` -> `pub fn qv_is_ident_byte` to avoid interpreter cross-module private collision.

## Verification & Honest Scope

- **Windows `--mode=interpreter` probe (`C:/dev/simple/bin/simple.exe`, `lsp_symbols` on `src/app/simple_lsp_mcp/main.spl`)**:
  - Request parsing (`extract_field` + `arg_field` path): `98,301 us` -> `4,090 us` (~24.0x faster).
  - Single `"public"` `lsp_handle_message`: `383.9 ms` (`383,858 us`) -> `211.6 ms` (`211,640 us`), output byte-for-byte identical (`1,671` bytes); `"all"` output byte-for-byte identical (`38,538` bytes).
  - 20 warm sequential `"public"` `lsp_handle_message` requests (`lsp_symbols_perf_spec.spl`): baseline `7,678 ms` total (`383 ms` avg, `410 ms` max) -> optimized `3,980 ms` total (`199 ms` avg, `205 ms` p95, `206 ms` max) with `0` subprocess starts and single-read per file verified via `query_visibility_symbols_payload_v1`.
- **Remaining Linux native gate**:
  - `Status` remains `open` because these benchmarks ran on Windows in `--mode=interpreter` without building/running a Linux native binary; `scripts/check/check-mcp-lsp-nfr-evidence.shs` must still be run on Linux against the compiled native executable to confirm native p95 `< 200 ms` and peak RSS `< 1 GiB`.
