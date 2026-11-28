# MCP server grows to multi-GB RSS over a long session (2026-11-24)

**Status:** items 1-4 fixed in source (`tok_record_at` bounded tail + append,
linear `rt_stdin_read_*_text` framing, byte-slice `escape_json`/`strip_ansi`,
linear `_ctx_load_stats` + coalesced `_ctx_stats_bump2`); NOT redeployed/measured
on a live multi-hour session. Structural `transient_scope` fix open.

## Measurements (read-only `/proc`, live server of an active session)

Process: `bin/release/x86_64-unknown-linux-gnu/simple_mcp_server` (built
2026-11-21 13:20, 2,251,992 bytes), started 2026-11-22 15:18:05 KST, one stdio
client, single thread. Sampled 2026-11-24 16:14-16:28 KST (uptime ~49 h).

| metric | value |
|---|---|
| VmRSS = VmHWM | 6,496,052 kB (RssAnon 6,494,704 kB, RssFile 1,348 kB) |
| VmSwap | 2,196,968 kB |
| anonymous total (RSS + swap) | ~8.7 GB; `[heap]` (brk) mapping alone is 9,230,108 kB |
| open fds | 3 (stdin/stdout sockets, stderr log of 0 bytes) |
| `/proc/<pid>/io` | rchar 220.4 GB, wchar 2.74 GB, syscr 41.2 M, syscw 470 k |
| growth while idle | none: RSS and swap identical in every 20 s sample over 14 min (16:14-16:28), all four io counters identical between 16:16 and 16:28, no tool call in that window |
| calls served | 616 `mcp__simple-mcp__*` tool calls in the client transcript; 612 ctx events in `telemetry.sdn` since process start (that ledger is shared by every server on this repo, so 612 is an upper bound for this process) |
| average growth | ~14 MB per tool call (8.7 GB / 616); ~178 MB per hour of uptime |

So the growth is per request, anonymous, all in the brk heap (many small and
medium `malloc`s, nothing file-backed, no fd leak). The per-call delta could
not be sampled directly: no tool call was made on the server during the watch
and the task forbade driving it.

## Root cause class

Every string made outside a transient scope is registered immortal
(`src/runtime/runtime_native.c:1886` `rt_core_register_string` ->
`rt_core_register_immortal_ptr` when `owner_scope == 0`), and the MCP serve
loop (`src/app/mcp/main.spl:386`) opens no scope. Every string temporary of
every request therefore lives until exit, and the question is which path
allocates most per call. Read for strings only: array and dict lifetime, the
8-bytes-per-element width assumed for `[u8]`, and the backend's
`rt_string_free` / `rt_array_free_deep` emission sites
(`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:1868`) were
not traced, so the per-byte figures below assume arrays and dicts are retained
the same way. The measured 8.7 GB against ~8 MB of total request and response
bytes is consistent with that.

## Ranked accumulators

1. **`tok_record_at`, `src/app/mcp/main_lazy_telemetry.spl` (line 151 before this change; fixed here).**
   Ran on every `simple_ctx_*` call and cost memory proportional to the whole
   ledger (`.simple/ctx/telemetry.sdn`, 76 KB / 1,265 rows now, ~39 KB when the
   process started), three ways:
   - `file_read(path)` twice (once directly, once inside `tok_load_events`);
   - `parse_sdn_table` over every row: `split_sdn_row`
     (`src/lib/nogc_sync_mut/database/core.spl:755`) makes a `chars()` array
     and one array + one joined string per cell, `strip_quotes` makes a second
     `chars()` array per cell, plus one `Dict` row and one `TokEvent` per row;
   - `file_atomic_write` of the whole ledger: the text goes through
     `external_text_from_internal` -> boxed `[u8]` -> `external_copy_bytes`
     (twice) -> decode back to text
     (`src/lib/nogc_sync_mut/io/file_external_compat.spl:39-53`,
     `src/lib/common/encoding/external_text.spl`), i.e. several 8-byte-per-byte
     arrays per write.
   Static estimate: 100-150 bytes retained per ledger byte, so ~6-9 MB per call
   at the average ledger size and ~8-11 MB now. That is roughly half of the
   measured 14 MB per call, and the only term that grows with history (total
   cost quadratic in calls). The constants are estimates from reading the
   source, not measurements.
2. **Stdin framing, `src/app/mcp/main.spl:276-295` (fixed in follow-up).**
   `_mcp_read_line` / `_mcp_read_chars` previously built the message with one
   `result + ch` per byte, so an n-byte request retained n^2/2 bytes. Replaced
   with linear `rt_stdin_read_line_text()` / `rt_stdin_read_chars_text(count)`
   (`runtime_native.c:4022,4043`, matching `src/app/md_lsp/md_lsp_main.spl`),
   plus a 64 MiB `Content-Length` cap (`_MCP_MAX_CONTENT_LENGTH`) and short-read
   EOF guard (`body.byte_len() < content_length`). Note: these are C-runtime
   primitives (Windows binary stdio mode set by `rt_win_set_binary_stdio`), not
   registered in the Rust seed interpreter (`src/compiler_rust/.../interpreter_extern`),
   matching `md_lsp_main.spl` / `tui_shell.spl`.
3. **`_ctx_stats_bump`, `src/app/mcp/main_lazy_ctx_tools.spl:481` (fixed in follow-up).**
   Two to three load + atomic rewrites of `stats.sdn` per call using the
   generic per-character `parse_sdn_table`. Replaced `_ctx_load_stats()` with a
   linear line parser and coalesced paired stat bumps via `_ctx_stats_bump2`.
4. **Response building (fixed in follow-up)**: `escape_json` and `strip_ansi`
   (`main_lazy_json.spl`) previously pushed one 1-char string per byte into
   `parts`. Replaced with byte-indexed scanning (`byte_at`) and slice runs
   (`substring(span_start, i)`), avoiding per-character allocations.
5. **Unexplained remainder**: about half of the 14 MB per call is not
   accounted for by 1-4. Not pinned.

Ruled out: the bounded child runner's 8 MiB capture buffers are freed
(`src/runtime/runtime_process_owned.c:4990-4992`); the 220 GB of `rchar` is its
`/proc` tree sampling through `fopen`/`fgets` with stack buffers
(`runtime_process_owned.c:106-146`), which allocates nothing persistent; the
BM25 chunk store (3.0 MB) is not reloaded per `simple_ctx_execute`, and only 2
searches and 2 batches ran. `wchar` of 2.74 GB (4.4 MB per call) is not
explained.

## Fix in this change

`tok_record_at` now reads at most the last 512 bytes of the ledger to get the
last row's id (`tok_next_id_from_tail`, pure) and appends one row with
`file_append_text`. It falls back to the previous whole-ledger path when the
tail cannot answer (no trailing newline, malformed last row, unreadable tail)
and when the ledger does not exist yet. Both primitives are bounded by the
bytes asked for, not the file: `external_file_read_bytes_at`
(`src/lib/nogc_sync_mut/io/external_file.spl:17`) `pread`s `size` bytes, and
the `FileMode.Append` branch of `FileTextSession.write_file`
(`src/lib/nogc_sync_mut/io/file_text_session.spl:168`) encodes only the new
content and seeks to EOF. Row format and every tool result are unchanged. The
next id is now last row + 1 where it was max + 1: equal on a ledger whose last
row carries the maximum, which the live one does (last = max = 1258). Ids were
never unique (the live ledger already has 7 duplicated ids from concurrent
servers) and nothing reads `.id` except this function. The ledger is no longer
replaced atomically on each event; it is appended like the chunk store.

## Not verified

- No build, no redeploy, no spec run: there is no deployed `bin/simple` on this
  host and a compiler build was running. The two new `it`s in
  `test/01_unit/app/mcp/token_stats_spec.spl` have not been executed.
- The running server (pid 1371272) still carries the old code and keeps its
  8.7 GB until it is restarted; a restart alone returns that memory.
- The per-call saving is the static estimate above.

## Open

- Structural fix: wrap each request in `transient_scope_begin/end`
  (`src/lib/nogc_sync_mut/sffi/transient.spl`). Precondition: every handler
  write to module state must be promoted or moved first, or it dangles at scope
  end. Known writers: `_CTX_CACHE_*` (`main_lazy_ctx_tools.spl:645-650`),
  `MCP_LOG_LEVEL` and `_MCP_TRANSPORT_MODE` (`main.spl`),
  `_systemd_scope_probe` / `_memscope_sequence` (`resource_scope.spl:248`),
  debug/play/assistant session registries.
- Item 5 (measure a fresh deployed server: RSS delta per call against ledger
  size) once a full release binary rebuild is deployed. (Follow-up standalone
  native probe verified `rt_stdin_read_line_text` / `rt_stdin_read_chars_text`
  64 KB framed + JSONL read at 5,040 KiB HWM and 50x `escape_json`/`strip_ansi`
  stress at 8,748 KiB HWM.)
- A `simple_ctx_execute` call hung until the client's 1,800 s timeout the same
  day. Not reproduced and not pinned. The server caps a ctx command at 120 s
  and the runner's post-timeout path (`runtime_process_owned.c:4840-4857`,
  TERM, grace, KILL, bounded post-reap drain) shows no unbounded wait on static
  reading. Unverified suspects: the server itself stalling on page-in with 2.2 GB
  swapped and the host's swap full; `systemd-run --user --scope` blocking
  before the child starts.

## Request-scope & retained-state fix (2026-11-28)
Implemented per-request transient scope cleanup around the MCP serve loop after
auditing cross-request globals and lazy caches, plus deduplicated ANSI stripping:

1. **Transient request-scope boundary in `src/app/mcp/main.spl` (`SIMPLE_MCP_REQUEST_SCOPE`):**
   - Extracted `_mcp_serve_one_iteration(request_scope_enabled: bool)` and
     `_mcp_end_request_scope(...)`, enabled by default and opt-out via
     `SIMPLE_MCP_REQUEST_SCOPE=0`.
   - Wraps each request read + dispatch cycle in `transient_scope_begin()`,
     pauses with `transient_scope_pause()` on exit paths, selectively promotes
     cross-request state only when mutated during that iteration, and closes
     with `transient_scope_end()`.
   - Keeps `src/app/mcp/main.spl` free of indented `use` or heavy tool imports
     (matching startup closure isolation constraints).

2. **Audited cross-request state promotion (`src/lib/nogc_sync_mut/sffi/transient.spl`, `main_lazy_dispatch.spl`, tool/session state modules):**
   - Exported `transient_scope_pause` and `transient_promote` from `transient.spl`.
   - Added `mcp_static_tools_promote_caches()` (`src/app/mcp/main_static_tools.spl`)
     to promote `_MCP_TOOL_TABLE_CACHE`, `_MCP_FULL_JSON_CACHE`, and
     `_MCP_LAST_READ_PATH` + `_MCP_HINT_SLOTS` on `simple_read` / `simple_edit` / `simple_multi_edit`.
   - Added `mcp_ctx_promote_caches()` (`src/app/mcp/main_lazy_ctx_tools.spl`),
     `mcp_session_state_promote()` (`src/app/mcp/main_session_state.spl`),
     `dap_sessions_promote()` (`src/app/mcp/dap_bridge.spl`),
     `lsp_mcp_view_promote()` (`src/app/simple_lsp_mcp/visibility_state.spl`),
     and `dialog_snapshots_promote()` (`src/app/mcp/main_lazy_dialog_tools.spl`),
     wired through `mcp_lazy_promote_static_caches()` and
     `mcp_lazy_promote_tool_state(tool_name)` in `src/app/mcp/main_lazy_dispatch.spl`
     so persistent caches/sessions survive `transient_scope_end()`.
   - Also promotes `_MCP_TRANSPORT_MODE` on `initialize` and `MCP_LOG_LEVEL` on
     `logging/setLevel`.

3. **ANSI helper deduplication (`src/app/mcp/main_lazy_diag_tools.spl`):**
   - Removed the duplicate per-character `pub fn strip_ansi` implementation and
     imported/re-exported `strip_ansi` from `.main_lazy_json`.

### Verification (2026-11-28)
- Added `test/01_unit/app/mcp/mcp_request_scope_spec.spl`.
- Full `simple test` execution on the Nov 16 Rust seed binary is blocked by
  pre-existing `src/lib/common/types.spl:23:19: Unexpected token: expected As, found Newline`.
- Self-contained seed execution (JIT and `SIMPLE_EXECUTION_MODE=interpret`)
  verified `rt_transient_array_scope_begin`, `rt_transient_array_scope_pause`,
  and `rt_transient_array_scope_end` all return `true`.
- Isolated seed syntax probe passed with zero parse errors across all modified
  MCP modules, `transient.spl`, and `mcp_request_scope_spec.spl`.
- Static source contract checks confirmed zero indented `use ` in `src/app/mcp/main.spl`,
  zero duplicate `pub fn strip_ansi(` in `main_lazy_diag_tools.spl`, and zero
  relative function-local `use .` imports in `main_lazy_dispatch.spl`.
- Item 5 (multi-turn RSS measurement on a freshly built pure-Simple binary) remains
  pending a release build deploy.
