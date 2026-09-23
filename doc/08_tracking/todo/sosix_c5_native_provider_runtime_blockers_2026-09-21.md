# SOSIX C5 native file providers: runtime integration blockers

Date: 2026-09-21. Status: **OPEN / provider not implemented**.

Audited source: `e0dd873da1b7828389db4eb60e82972cc8245313` (`origin/main`).
Isolated worktree: `D:/wk-sosix-async-file-306`.

## Record and acceptance

`doc/08_tracking/todo/todo_db.sdn` row **306**, P3, remains OPEN:
`(sosix C5) add the macOS and Windows providers on a host that has them; this`
at `src/lib/nogc_async_mut/sosix/file_driver.spl:16`.
Row 33 contains an older, closed entry for the same source location whose
"no IOCP/Windows async-file externs" explanation is incomplete. This audit
does not change either database row or count the closed duplicate as delivery.

Acceptance requires a real platform provider connected to the SOSIX lifecycle:

- Submit positioned reads/writes without executing the file operation in the
  SOSIX submission/service path; preserve offsets, short transfers, and errors.
- Hold each operation's capability and buffer until the OS completion or
  cancellation is observed; reclaim resources after retirement.
- Select the available provider honestly, including an explicit fallback when
  native support is unavailable.
- Execute provider selection and file lifecycle unit/SSpec regressions against
  the source-matched native runtime on Windows and macOS. Windows C evidence
  must use the exact approved LLVM 23.1.1 compiler.

## Findings

| Evidence | Consequence |
|---|---|
| `file_driver.spl` calls `file_read_text_at`/`file_write_text_at` inside `service`, then `complete_taken` | This is real filesystem service, performed synchronously. Existing fallback tests do not prove a native async provider. |
| `src/runtime/platform/async_windows.c` implements overlapped `ReadFile`/`WriteFile` and IOCP polling | Windows backend source exists. A blanket claim that no IOCP code exists is incorrect. |
| `src/runtime/platform/async_macos.c` describes kqueue plus worker threads for file I/O | macOS backend source also exists; it has no verification result in this Windows audit. |
| `scripts/check/runtime_source_list_parity_baseline.txt` lists `platform/async_driver.c`, `async_windows.c`, and `async_macos.c` with membership `none` | None participates in the seed C capsule, self-hosted native runtime, or Rust runtime C source list. Direct inspection of the three list owners confirms no async platform entries. |
| No `rt_driver_*` binding or platform provider selection appears in `src/lib/nogc_async_mut/sosix` | The dormant bridge is not a SOSIX provider. |
| `async_driver.c` disagrees with `runtime.h` on connect/open argument lists and backend-name return type | Simply adding source files to a runtime list does not establish a valid public ABI. |
| `src/compiler_rust/runtime/src/async_driver_sffi.rs:272` handles Windows read/write/open/close/fsync with `NEG_ENOSYS` (`-38`); its backend name is `rust-syscall` | Seed symbols are not evidence of an IOCP provider. |

The source-list owners are
`src/compiler_rust/compiler/src/pipeline/native_project/tools.rs`,
`src/compiler/70.backend/backend/runtime_compiler.spl`, and
`src/compiler_rust/runtime/build.rs`. No implementation files were changed.

## Windows compiler evidence

Compiler:
`C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc/bin/clang-cl.exe`

Version: `clang version 23.1.1`, LLVM commit
`6dfe1677ab8dffbc6ec13d53a1e0215d75147689`.

Compiler SHA-256:
`D43B7FA07B5B77B716E60600AD2792CFB2EEB370AECB6144BF6C698F2C6D7467`.

Run from the worktree root in PowerShell; each command records its compiler
exit code independently. The Visual Studio developer environment supplies
the Windows SDK and libraries; `clang-cl.exe` is the compiler for both runs.

```powershell
New-Item -ItemType Directory -Force -Path build/todo306 | Out-Null
cmd.exe /d /s /c 'call "C:\Program Files\Microsoft Visual Studio\2022\Community\Common7\Tools\VsDevCmd.bat" -arch=x64 -host_arch=x64 >nul && "C:\dev\tool\clang+llvm-23.1.1-x86_64-pc-windows-msvc\bin\clang-cl.exe" /nologo /W4 /WX /c /I src\runtime /Fobuild\todo306\async_windows.obj src\runtime\platform\async_windows.c' *> build/todo306/async-windows-compile.log
$LASTEXITCODE # Observed: 0
cmd.exe /d /s /c 'call "C:\Program Files\Microsoft Visual Studio\2022\Community\Common7\Tools\VsDevCmd.bat" -arch=x64 -host_arch=x64 >nul && "C:\dev\tool\clang+llvm-23.1.1-x86_64-pc-windows-msvc\bin\clang-cl.exe" /nologo /W4 /WX /c /I src\runtime /FI src\runtime\runtime.h /Fobuild\todo306\async_driver_header_contract.obj src\runtime\platform\async_driver.c' *> build/todo306/async-driver-header-contract.log
$LASTEXITCODE # Observed: 1
```

The second command reports four errors: one existing `strdup` deprecation
promoted by `/WX`, and three independent incompatible function declarations:

| Function | Public header | Dormant C bridge |
|---|---|---|
| `rt_driver_submit_connect` | `handle, fd, addr, addr_len, port` | `handle, fd, addr, port` |
| `rt_driver_submit_open` | `handle, path, path_len, flags, mode` | `handle, path, flags, mode` |
| `rt_driver_backend_name` | returns `int64_t` | returns `const char*` |

Observed SHA-256 values (source hashes describe this Windows checkout):

| File | SHA-256 |
|---|---|
| `src/runtime/platform/async_driver.c` | `C58C05CE633165874568AF4958EAC93873737191CE2059692578F01C7F210F6D` |
| `src/runtime/platform/async_windows.c` | `628D4E127379CAF68E255C7A4F653E798859198E71B31D7E466EC449FB8E3844` |
| `src/runtime/platform/async_macos.c` | `C9335B6F16D66AC005A604A5285611B9E2D2835E654E1290A6B7FAE6F9D96D43` |
| `build/todo306/async_windows.obj` | `F29530E1B35A7375BE74D35DD8D16AEAE9097C8A4E2602CDAA0121B41B2D61C7` |

This is compile evidence and a failing ABI-contract reproduction. There was
no native provider execution, no new unit/SSpec PASS, and no performance or
memory improvement claim. macOS execution remains unverified.

## Required prerequisite work

Reconcile the public ABI and text/buffer ownership, integrate the platform
sources in the intended runtime builds, and review completion cleanup and
cancellation before exposing a Simple adapter. Then implement provider
selection and the SOSIX operation mapping, and obtain native behavioral
evidence on each platform. These are remaining implementation tasks, not
conditions satisfied by compiling one standalone C file.
