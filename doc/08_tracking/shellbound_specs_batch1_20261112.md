# Shell-bound specs port — batch 1 ledger (2026-11-12)

Family: integration specs whose harness is POSIX-shell-scripted and RED on
native Windows. Source list: `build/phase2-runner/fails_so_far.txt` re-filtered
for `rm -rf` / `/bin/sh` / `shell(` (86 specs after excluding `*_log_modes_spec`
and the `.simple_result_*` scratch file).

Worktree: `work/fix-shellbound-specs-20261112` off `origin/release/1.0.0`.

## Root-cause findings (apply to the whole family)

- **RC-1 (harness):** specs that declare `extern fn rt_process_run` and spawn
  `/bin/sh`, `/bin/test`, `mktemp` directly bypass the std facade
  (`std.nogc_sync_mut.io.process_ops.process_run`), which on Windows resolves
  POSIX tool paths onto the Git-for-Windows userland
  (`_resolve_posix_tool`, process_ops.spl:984). Raw extern spawns return exit
  code -1 on native Windows. Port: swap the raw extern for the std facade
  (`process_run`) or the shared CLI spawn fixture
  (`test/helpers/simple_cli_spawn_fixture.spl`).
- **RC-2 (seed quirks encountered while porting):**
  - `}}` inside a string literal is the escape for a literal `}`, so JSON
    bodies built as one literal ending `}}}` lose their final brace (latent on
    ALL hosts, not Windows-specific).
  - `env_get` returns `""` for unset variables; defaults need `env_get_or`
    (`??` never falls back).
  - Direct tuple-destructuring of a call to a helper fn that internally
    `match`es a `Result` fails to compile ("semantic: value is not callable");
    inline the `match` at the use site (the `send_mcp` shape) instead.

## Per-spec classification (batch 1)

| Spec | Class | Result |
|---|---|---|
| test/02_integration/app/snpm_mkdir_spec.spl | harness-portable | GREEN 1/1 — mktemp//bin/sh//bin/test replaced with secure_temp_dir/file_create_exclusive/is_dir/file_exists/dir_remove_all |
| test/02_integration/app/io_runtime_import_spec.spl | harness-portable | GREEN 9/9 — host_os oracle aligned to the documented platform_name() table (windows/illumos/solaris/simpleos were missing); io_runtime shell facades were already host-aware |
| test/02_integration/app/mcp_stdio_integration_spec.spl | harness-portable + product bug PB-3 | 14/16 GREEN; 2 editor examples blocked by PB-3 |
| test/02_integration/bootstrap/macos_process_live_spec.spl | host-gate (macOS-only surface) | 3 honest skips, verdict OK |
| test/02_integration/bootstrap/macos_process_live_tmpdir_expansion_spec.spl | host-gate (macOS-only surface) | 1 honest skip, verdict OK |
| test/02_integration/app/query_visibility_surfaces_spec.spl | harness-portable + product bug PB-2 | ported to simple_cli_run; 6/6 examples blocked by PB-2 |
| test/02_integration/app/query_visibility_workspace_symbols_spec.spl | harness-portable + product gap PB-4 | ported to simple_cli_run; 3/3 examples blocked by PB-4 |
| test/02_integration/app/scv_changeid_spec.spl | harness-portable + product bug PB-1 | extern->facade swap done; 4/4 examples blocked by PB-1 |

Counts batch 1: 2 green, 2 host-gated, 4 ported-but-red (all four blocked by
product bugs/gaps below, kept RED deliberately — skip-gating would hide them).

## Product bugs / gaps filed (evidence attached; NOT worked around in specs)

- **PB-1 scv cannot run under the seed interpreter (P1).**
  `bin/simple run src/app/scv/main.spl snapshot` fails with
  `error: semantic: ... unknown extern function: rt_file_modified_time`.
  The runtime implements it (`src/compiler_rust/runtime/src/value/sffi/file_io/metadata.rs:359`)
  but the seed interpreter dispatch table never registers it: zero matches for
  `rt_file_modified` in `src/compiler_rust/compiler/src/interpreter_extern/`
  (`insert_simple!` table at mod.rs:1606-1636 registers rt_file_hash/rt_file_size/rt_file_stat only).
  Blocks all 61 scv_* specs. Host-independent in source; observed wherever the
  seed is the runtime. Related known interpret-lane defect:
  doc/08_tracking/bug/rt_file_stat_returns_size_on_interpret_lane_2026-09-19.md.
- **PB-2 query_visibility semantic-tokens path does not compile (P1).**
  `src/app/cli/_QueryVisibility/query_commands.spl:237` calls
  `token_name_at(file_path:..., token_line:..., token_col:..., token_len:...)`
  but the parameters are named `(file, line_num, col, length)`
  (`symbol_resolution.spl:251`). The deployed compiler rejects unknown named
  arguments; the whole query_visibility graph fails for every subcommand on
  the interpreter lane (`error: semantic: in call to 'token_name_at' ...
   unknown argument 'file_path'`). Verified host-independent with a minimal
  probe. Note: the JIT lane reports the same error for this program (the
  module cannot be demoted), so `bin/simple run src/app/cli/query_visibility.spl
  <anything>` exits 1 today.
- **PB-3 MCP editor tools can never see their arguments (P1).**
  `src/app/mcp/main_editor_tools.spl:23-31`: `handle_editor_mcp_open_file`
  receives the tool `arguments` object from the lazy dispatcher
  (`main_dispatch.spl:639-642`, body = args), but `editor_mcp_argument`
  expects the full request body and does `extract_field_raw(body, "params")`
  first — which is always "null" on the arguments object, so every call
  returns `-32602 missing path argument` (read_buffer/list_open_files return
  `-32602 no active buffer`). Reproduced end-to-end against
  `bin/simple_mcp_server.cmd` source mode; the extractor itself is fine when
  fed a full body. Host-independent; blocks mcp_stdio editor examples.
- **PB-4 query_visibility workspace-symbols emits no visibility metadata and
  no boundary filtering (P2, oracle-vs-product gap).**
  `bin/simple run src/app/cli/query_visibility.spl workspace-symbols --query
  lsp_main --requester src/lib/nogc_sync_mut/lsp/main.spl` exits 0 but returns
  plain LSP JSON (`[{"name":"lsp_main","kind":12,"location":...}]`) with no
  `simpleVisibility`/`display` fields, and a cross-boundary private query
  (`--query query_visibility --requester src/lib/nogc_sync_mut/lsp/main.spl`)
  returns private `app.cli` symbols instead of `[]`. The spec oracles expect
  the documented visibility envelope. Needs owner triage: implement or
  re-spec.

## Notes

- PB-1..PB-4 were left RED in the ported specs on purpose; fixing them is
  product work outside this lane (only specs + genuinely-broken shared helper
  may be touched).
- The remaining 78 family specs are expected to follow the same three
  patterns: facade swap (scv family, blocked by PB-1 until the seed
  dispatch table registers rt_file_modified_time), CLI-fixture swap, or
  host gates.
