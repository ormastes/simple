# Feature: simple_core runtime completeness for the core-c lane (2026-06-02)

**Feature ID:** #FR-SIMPLECORE-001
**Category:** Runtime / Bootstrap
**Status:** Proposed
**Motivation bugs:** `core_c_string_len_registry_2026-06-02.md`,
`core_c_stdin_fgetc_hang_2026-06-02.md`

## Goal

Make the pure-Simple `simple_core` runtime (`src/runtime/simple_core/*.spl`)
complete enough to be the runtime for the core-c native lane, replacing the
hand-written C runtime (`src/runtime/runtime_native.c` …). This realizes the
"interpreter/compiler/lib/runtime in pure Simple, C only where required"
direction and fixes the two core-c blockers by construction (`simple_core`
already has a registry-free `rt_string_len` and a `read()`-based
`stdin_read_char`).

## Gap (measured 2026-06-02)

The MCP native binary pulls **173** runtime symbols. `simple_core` exports 217
`pub fn`s but is **missing 58** of those 173. Categories:

| Category | Count | Symbols |
|---|---|---|
| TCP / networking | 16 | `rt_io_tcp_bind/accept/accept_timeout/connect/connect_timeout/read/read_line/write/write_text/flush/close/shutdown/local_addr/peer_addr/set_nodelay/set_read_timeout/set_write_timeout` |
| File / dir I/O | 10 | `rt_file_open/close/move/remove/read_bytes/write_bytes/read_text_at/write_text_at`, `rt_dir_list/remove_all` |
| Process | 7 | `rt_process_spawn/spawn_async/wait/kill/is_running`, `rt_get_argc/get_args` |
| Dict | 5 | `rt_dict_get/set/keys/values/len` |
| Channel | 5 | `rt_channel_new/send/recv/try_recv/close` (+`is_closed`) |
| Bytes | 3 | `rt_bytes_from_raw/u8_at/u8_set` |
| Text | 3 | `rt_string_char_code_at`, `rt_string_trim_start`, `rt_text_count_codepoints` |
| Misc | ~9 | `rt_print`, `rt_println`, `rt_getpid`, `rt_tuple_len`, `rt_unwrap_or_self`, `rt_is_debug_mode_enabled`, `rt_process_is_running`, `spl_thread_cpu_count` |

(Full list captured during the audit; regenerate with the method in the plan
doc.)

## Difficulty tiers

- **Easy (~15):** `rt_print/println/getpid/tuple_len/trim_start/char_code_at/
  text_count_codepoints`, dict + bytes ops — thin Simple logic.
- **Moderate (~17):** file/dir I/O + process — `extern` syscall + Simple logic,
  same pattern as the existing `read`/`write`/`malloc` wrappers in `simple_core`.
- **Larger (~26):** TCP (16) + channels (5+) — real syscall/concurrency surface.
  The MCP is stdio-only, so TCP is only needed because linked tool code
  references it; trimming that code could defer this tier.

## Acceptance

- core-c native binaries that link `simple_core` (not `runtime_native.c`) pass:
  `"abc".len() == 3`; stdin EOF terminates; `scripts/check/check-mcp-native-smoke.shs`
  reports `mcp_tools_json_valid=true`, `mcp_wm_text_tools_present=true`.
