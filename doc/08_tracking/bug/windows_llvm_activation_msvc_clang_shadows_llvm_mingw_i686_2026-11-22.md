# Windows LLVM activation puts MSVC-target clang ahead of llvm-mingw

- **Status:** open
- **Severity:** P2 (i686/x86_64 GNU lanes can silently compile with the MSVC-default clang)
- **Area:** toolchain / `~/.simple/toolchains/activation/windows-llvm-23.1.1.shs` (and `.ps1`)
- **Found:** 2026-11-22, Windows i686 cross-link lanes (native linker + pure-Simple linker)

## Symptom
The activation script prepends
`llvm-msvc-23.1.1/clang+llvm-23.1.1-x86_64-pc-windows-msvc/bin` to `PATH`
(line 13). That directory ships `clang.exe`/`clang-cl.exe` whose default
target is `x86_64-pc-windows-msvc`. After sourcing it, any lane that resolves a
bare `clang`/`cc` for the i686-w64-mingw32 (or x86_64 windows-gnu) target gets
the MSVC-target driver instead of llvm-mingw
(`~/.simple/toolchains/llvm-mingw-20260922-ucrt-x86_64/bin`), contrary to the
toolchain policy (Windows default = llvm-mingw UCRT; MSVC is the optional
`--msvc` lane).

Workaround used: pass `CC=<llvm-mingw>/i686-w64-mingw32-clang.exe` explicitly.

## Fix direction
The activation exists to provide `LLVM_SYS_231_PREFIX` / `LLVM-C.dll` for the
seed's `llvm` cargo feature. It should export those without putting the MSVC
clang driver first on `PATH` (or put llvm-mingw's bin ahead of it). The
generator of this script (bootstrap-prereqs / setup) is the place to change.
