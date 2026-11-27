# Windows C `rt_process_run` reports exit 0 for every command

**Status:** C source repair qualified on Windows GNU (2026-10-30); deployment
still requires a runtime-capsule re-cut. Existing Simple wrappers retain their
bounded-owner workaround.
**Host:** Windows x86_64-pc-windows-msvc, C runtime `src/runtime/runtime_native.c`.

## 2026-10-30 Windows GNU follow-up

A production-C probe at PR #5342 head `44bc6a945ce` reproduced this defect
through `rt_process_run_tuple`: expected nonempty stdout/stderr and exit 7,
observed empty payloads and exit 0. Replacing only `runtime_native.c` with
the pre-#5342 merge-parent version gave the same failure. This is not a
regression from the tuple-owner free. The timeout, bounded-text and bounded-byte
facades all passed payload/status checks after 32 allocator-reuse cycles.
Evidence is retained at `C:/dev/process-tuple-windows-5342-20261030/result.sdn`,
with `run.log` and `baseline-run.log` alongside the exact source snapshots.

The Windows-only repair delegates the array owner to
`rt_process_run_bounded(cmd, cmd_len, args, 0, -1)`. The Windows owner accepts
zero as no deadline and -1 as uncapped text capture. Both public array and
native tuple ABI facades reach this owner; POSIX behavior remains unchanged.

The new regression compiles eight real production runtime modules, without
stubs, through `scripts/check/check-windows-unbounded-process.shs`. It checks
both ABIs, statuses 7/300/missing executable, argv quoting, Unicode, executable
paths containing spaces, output above 4 MiB on both streams, and payload
lifetime after owner release. No compiler-bootstrap or Darwin leak result is
implied by this focused C gate.

Initial qualification exposed a separate existing limitation: the text-capture
owner uses `CreateProcessA`, while only its byte mode uses `CreateProcessW`.
A UTF-8 executable path therefore fails on this host's non-UTF-8 ANSI codepage.
The first build also needed the harness to select wide `wmain` startup without
changing production SDK macros (`-municode -UUNICODE -U_UNICODE`).
Logs: `C:/dev/windows-unbounded-process-check-20261030.log` and
`C:/dev/windows-unbounded-process-check-20261030-v2.log`.

Text capture now shares the existing strict UTF-8-to-UTF-16 command conversion
and filtered wide environment with byte capture. Both use `CreateProcessW` and
`STARTUPINFOEXW`; byte payload/cap semantics are unchanged. The unrelated piped
process owner's ANSI environment helper is retained. Removing that shared
helper initially caused a compile failure, recorded in
`C:/dev/windows-unbounded-process-check-20261030-v3.log`, then corrected.

The focused production-C gate passed all 25 cases (five cases each through
array, unbounded tuple, timeout tuple, bounded text tuple and bounded byte
tuple), exit 0. Large stdout is exactly 4,194,427 bytes and stderr exactly
4,194,321 bytes, with every byte checked. Compiler:
`C:/Users/user/.simple/toolchains/llvm-mingw-20260922-ucrt-x86_64/bin/clang.exe`;
log: `C:/dev/windows-unbounded-process-check-20261030-v4.log`.
The build emitted only the existing unrelated pointer-sign warning in
`rt_win_private_atomic_write`. No full-bootstrap, MSVC, Darwin leak, or deployed
runtime claim follows from this Windows GNU C result.

Independent review also found that the capture owner allocated the inherited
handle allowlist but never attached it to startup information. The repair sets
`startup.lpAttributeList = attributes`. A focused additional `inheritance` case
passes through all five facades: Unicode environment key/value survives,
`_SIMPLE_STACK_SET` is filtered, an unrelated inheritable event handle is absent
in the child, and stdout/stderr/exit 7 remain correct. Those five cases passed
on the final owner (exit 0), log
`C:/dev/windows-unbounded-process-check-20261030-v5.log`. The preceding 25-case
PASS was not rerun; the final handle-list change was qualified with these five
representative real child launches. Set `SIMPLE_PROCESS_PROBE_CASE=inheritance`
to run only that focused addition; absent a filter, the gate runs all 30 cases.
Unknown case selections fail closed with exit 2 before compilation; the typo
rejection was checked separately in
`C:/dev/windows-unbounded-process-filter-rejection-20261030.log`.

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

## Original repair recommendation (now implemented above)

Fix `rt_process_run_array` for `_WIN32`, either by delegating to `rt_process_run_bounded(cmd, len, args, 0, -1)` or by
dropping the POSIX quoting and `>> 8`. Direct `rt_process_run` callers that bypass the std wrappers are still
affected: for example `src/compiler/70.backend/backend/runtime_compiler.spl:287`.
