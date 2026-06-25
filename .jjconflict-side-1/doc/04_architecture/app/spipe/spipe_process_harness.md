<!-- codex-design -->
# SPipe Process Harness Architecture

## Pattern

Use a common library with thin provider adapters:

- `src/lib/nogc_async_mut/spipe_process_harness/types.spl`
- `src/lib/nogc_async_mut/spipe_process_harness/core.spl`
- `src/app/spipe_process_harness/main.spl`

## Flow

Provider hook -> `simple spipe-process-harness hook` -> normalize provider/event -> read `.spipe/<feature>/state.md` -> gate -> append `.spipe/<feature>/events.jsonl` -> return allow/block exit code.

## Hot Path

The hook path performs one state read, one JSONL append, and no full-tree scans. HUD can call `jj` because it is an explicit operator command, not a hook hot path.

## Startup and Latency Targets

- Hook startup: less than 100 ms after compiled artifact warmup.
- Hook request handling: no subprocesses in the provider hook path.
- HUD: less than 500 ms, including `jj` calls.

