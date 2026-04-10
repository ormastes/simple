# mcpgdb Status And Remaining Plan 2026-04-02

## Summary

`mcpgdb` is implemented and usable through the repo-local runtime entrypoint at `src/app/mcpgdb/main.spl`.

The main runtime blockers that existed earlier in the work are now closed:
- cold `initialize` no longer trips the watchdog
- lightweight session/state tools run through the live MCP wrapper
- backend-bearing `debug_command_run` works through the live wrapper
- compiled `.smf` runner caching is enabled by default again

The feature is not fully complete yet because runtime cleanup and broader end-to-end validation still remain.

## What Is Done

### Canonical runtime path

- The practical runtime path is `src/app/mcpgdb/main.spl`.
- The wrapper acts as a cold frontend and dispatches heavy work into narrower runners.
- The example tree remains at `examples/mcpgdb/`, but it is no longer the recommended live entrypoint.

### Split runtime architecture

- `src/app/mcpgdb/main.spl` handles MCP framing, `initialize`, `tools/list`, and runner dispatch.
- `src/app/mcpgdb/debug_state_runner.spl` handles lightweight state and registry calls.
- `src/app/mcpgdb/debug_session_runner.spl` handles session lifecycle calls.
- `src/app/mcpgdb/debug_exec_runner.spl` handles `debug_command_run`.
- `src/app/mcpgdb/debug_runner.spl` and `src/app/mcpgdb/clangd_runner.spl` remain the broader heavy runners.

### Live runtime verified

The following flows were verified successfully through `bin/simple run src/app/mcpgdb/main.spl`:

- `initialize`
- `debug_session_create`
- `debug_session_list`
- `debug_command_run(session_id="dbg_1", command="show version")`

### Compiled runner cache restored

- Compiled runner caching is enabled by default in `src/app/mcpgdb/main.spl`.
- The cache currently writes artifacts under `/tmp/mcpgdb_compiled__/`.
- Verified compiled artifacts include:
  - `src_app_mcpgdb_debug_session_runner.smf`
  - `src_app_mcpgdb_debug_exec_runner.smf`
- Source fallback is still kept as a guardrail if compile fails, runner execution fails, or the runner returns malformed output.

### Validation already completed

- `bin/simple check src/app/mcpgdb/*.spl`
- `bin/simple test examples/mcpgdb/test/unit`
- `bin/simple test doc/06_spec/app/compiler/feature/mcpgdb_spec.spl`

## What Was Fixed (2026-04-02, cleanup pass)

### Process cleanup hardened

- `stop_session_process()` now uses 3-stage shutdown: graceful `quit` via FIFO → `pkill -P` for child tree → SIGTERM → SIGKILL fallback with `ps_is_alive` verification
- Both copies hardened: `debug_backend_common.spl` and `backend_common.spl`
- Duplicate `stop_session_process_local()` in `debug_session_runner.spl` removed; now imports from `debug_backend_common`

### MCP wrapper exit cleanup

- `main.spl` calls `cleanup_all_sessions()` on EOF exit, killing all active debug sessions and clangd
- Signal handler integration added (best-effort, forward-compatible with SFFI when implemented)
- Temp request file leak fixed on write failure path

### clangd shutdown protocol

- `stop_clangd_workspace()` now sends LSP `shutdown` + `exit` before killing the process
- Same SIGTERM → SIGKILL escalation with child tree handling

### Stale session cleanup

- `cleanup_stale_sessions()` added to `debug_backend_common.spl`
- Called on runner startup after `load_persisted_state_safe()` — removes sessions whose processes are already dead

### Live smoke tests added

- `examples/mcpgdb/test/unit/cleanup_spec.spl` covers:
  - Session close proves gdb child process exits (before/after pgrep comparison)
  - Two concurrent sessions maintain state isolation
  - clangd tool path responds through runner

## What Remains

### Broader heavy-path validation

The following still need explicit live smokes:

- structured debug tools beyond `debug_command_run`
- remote backend flows for `openocd_gdb` and `t32_gdb`
- session restart / disconnect flows

### Compiled artifact lifecycle

- Cached `.smf` artifacts in `/tmp/mcpgdb_compiled_*/` have no TTL or cleanup
- Consider adding a cache invalidation pass on startup or a max-age check

### Example/runtime alignment cleanup

- Keep docs pointing to `src/app/mcpgdb/main.spl` as the live runtime path.
- Continue trimming stale references that imply the example entrypoint is the production wrapper.

## Helpful Facts

### Important SMF finding

The earlier assumption that compiled `.smf` execution was generically broken turned out to be too broad.

What actually matters is the source shape:

- script-style sources with top-level execution can compile to tiny stub `.smf` outputs
- proper `fn main()` runner files compile to real runnable `.smf` artifacts

That distinction explains why the `mcpgdb` runner cache now works: the split runner files are proper executable modules.

### Current cache behavior

- Cache artifacts are created on demand by `src/app/mcpgdb/main.spl`.
- The cache key is path-based, rooted under `/tmp/mcpgdb_compiled__`.
- The wrapper still falls back to source execution if the cached path is not usable.

### Current session/runtime state locations

- compiled runners: `/tmp/mcpgdb_compiled__/`
- session state: `/tmp/mcpgdb_state__.txt`
- per-session debugger files: `/tmp/mcpgdb_dbg_*`

These locations are the first places to inspect when runtime behavior looks inconsistent.

## Recommended Next Steps

1. Fix debugger child cleanup in `src/app/mcpgdb/debug_backend_common.spl` and the session-close path.
2. Add one live smoke for `debug_session_close` that proves the debugger child exits.
3. Add one live smoke for a clangd-backed tool through `src/app/mcpgdb/main.spl`.
4. Add one live smoke for two concurrent sessions to confirm state isolation.
5. Re-run verification after cleanup changes and update this note with final runtime status.
