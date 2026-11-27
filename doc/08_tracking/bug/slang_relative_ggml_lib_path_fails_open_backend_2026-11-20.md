# Relative `SLANG_GGML_LIB` fails `open_backend` under the release seed

- **ID:** slang_relative_ggml_lib_path_fails_open_backend_2026-11-20
- **Status:** OPEN (callers pass an absolute path)
- **Seed:** `C:/dev/seeds/simple-release.exe`, Windows, llvm-mingw shim

## Symptom

From the worktree root, `SLANG_GGML_LIB=build/sffi/slang_ggml.dll` made
`open_backend` return `LibraryNotFound` ("backend library could not be
opened") although the file exists; the same run with
`SLANG_GGML_LIB=C:/.../build/sffi/slang_ggml.dll` loaded the shim and passed
(2026-11-18, `build/probe/handles_probe.spl`). The default relative path in
`engine_lib_path()` (`build/sffi/slang_ggml.dll`) is affected the same way.

## Suspected cause

Not isolated. `_preload_windows_dll_siblings` derives the sibling directory
from the given path, and `spl_dlopen` resolves a relative path against the
loader search order rather than the process cwd; either can miss.

## Workaround

Pass an absolute `SLANG_GGML_LIB`. Fix: absolutize the path against the cwd
in `engine_lib_path()` / `open_backend` before `spl_dlopen`.
