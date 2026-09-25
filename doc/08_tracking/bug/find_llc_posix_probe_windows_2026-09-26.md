# `find_llc` resolves a nonexistent `llc-20` on Windows

**Status:** open. **Host:** Windows x86_64-pc-windows-msvc, stage-2 self-hosted `simple_cli.exe`.

## Symptom

`compile hello.spl -o hello.smf` prints `find_llc: env_dirs=0 first=<none> resolved=[llc-20]`.
The host has `llc.exe` only, from LLVM 23.1.1 under `C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc/bin`.
No `llc-20` exists.

## Code

`src/compiler/95.interp/interpreter/llvm/tools.spl`:

- `find_llc` (`:124`) tries `llc-20` … `llc` through `_find_tool`.
- `_env_tool_dirs` reads only `SIMPLE_LLVM_BIN` and `LLVM_SYS_180_PREFIX`. The Windows MSVC bootstrap env
  unsets `LLVM_SYS_180_PREFIX` (LLVM 23 is the authority), so `env_dirs=0`. `LLVM_SYS_231_PREFIX`
  and `SIMPLE_LLVM_WIN_ROOT_23` are not consulted.
- `_find_tool` (`:95`) runs `command -v {candidate} >/dev/null 2>&1` through `backend_shell_tuple`, which
  is `cmd.exe /c` on Windows (`70.backend/backend/io_compat.spl:13`). `command` and `/dev/null` are
  POSIX-only. `_tool_runs` then runs the bare candidate with `--version`. Only a zero exit status from one
  of these can have returned `llc-20`.

The result feeds the `llc` step of the LLVM text backend. That step failed without an error and produced a
0-byte SMF: see `smf_zero_code_bytes_llc_failure_masked_windows_2026-09-26.md`.

## Wanted

- Consult `LLVM_SYS_231_PREFIX` / `SIMPLE_LLVM_WIN_ROOT_23` in `_env_tool_dirs`.
- Skip the POSIX `command -v` probe on Windows. `where` already follows it.
- Confirm what `process_run` returns for a missing executable on Windows, since `_tool_runs` relies on it.
- The trace comment at `:133` says "Remove once the lookup is fixed". Remove the `print` when fixed.
