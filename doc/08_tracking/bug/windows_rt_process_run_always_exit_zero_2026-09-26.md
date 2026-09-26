# Windows C `rt_process_run` reports exit 0 for every command

**Status:** worked around in Simple (routed to the bounded owner on Windows); the C defect itself is still open.
It needs a runtime-capsule re-cut, which the runtime owner has to do.
**Host:** Windows x86_64-pc-windows-msvc, C runtime `src/runtime/runtime_native.c`.

## Evidence

The probe was native-built by the admitted stage-2 compiler against the host-gpu runtime capsule, then run directly:

| call | `process_run` (C `rt_process_run`) | `process_run_bounded(cmd, args, 0, -1)` |
|---|---|---|
| `cmd.exe /c exit 3` | 0 | 3 |
| `cmd.exe /c llc-20 --version` (missing tool) | 0 | 1 |
| `llc-20 --version` (missing executable) | 0 | -1 |
| `cmd.exe /c exit 300` | 0 | 300 |

## Cause

`rt_process_run_array` in `runtime_native.c`, reached through `rt_process_run_tuple`:

1. It builds the command line with `rt_core_shell_quote`, which uses POSIX single-quote quoting, and runs it with
   `popen` (`_popen`, meaning `cmd.exe /c`). `cmd.exe` does not understand `'...'`, so the command
   never starts: `'C:...' is not recognized`, and cmd exits 1.
2. It decodes the status with `status >> 8`, the POSIX wait-status layout. On MSVC `_pclose` returns
   the child's raw exit code, so every code below 256 becomes 0.

The combined effect is that nothing runs and success is reported. Consequences seen this session:
- `find_llc` resolved a nonexistent `llc-20`.
- `llc` "succeeded" without writing an object, so SMFs had a size-0 `main`.
- The `xxd` SMF writer (fixed in #1606) wrote nothing and still reported success.

## Workaround landed

`std.nogc_sync_mut.io.process_ops._process_run_raw` and `std.nogc_sync_mut.io_runtime._io_runtime_process_run_raw`
now use `rt_process_run_bounded` on Windows. That owner (`runtime_process.c`, `win_process_run_capture`) uses
`CreateProcessA` and `GetExitCodeProcess`.

## Remaining

Fix `rt_process_run_array` for `_WIN32`, either by delegating to `rt_process_run_bounded(cmd, len, args, 0, -1)` or by
dropping the POSIX quoting and `>> 8`. Direct `rt_process_run` callers that bypass the std wrappers are still
affected: for example `src/compiler/70.backend/backend/runtime_compiler.spl:287`.
