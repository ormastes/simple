# Unqualified Windows native-build under Git Bash links GNU against MSVC objects

Status: OPEN; owner decision needed (default flavor for an unqualified target
on a Windows host). Workaround: pass `--target x86_64-pc-windows-msvc`.

## Reproduction (2026-10-18, Stage 2 compiler from release_phase3 e77412a8eef)

Git Bash sets `MSYSTEM=MINGW64`. A 20-line `native-build` with no `--target`,
`CC` = LLVM 23.1.1 release `clang.exe` (MSVC default triple), core-C runtime:

```text
ld.lld: error: undefined symbol: __stdio_common_vfprintf
ld.lld: error: undefined symbol: __chkstk
ld.lld: error: undefined symbol: _fltused
ld.lld: error: undefined symbol: __p__environ
```

Same program and `CC` with `--target x86_64-pc-windows-msvc`: links, runs,
prints the expected output (rc=0).

## Cause

`windows_link_flavor_select` (`70.backend/backend/runtime_compiler.spl`) picks
`gnu` for an unqualified target whenever `MSYSTEM` is set, so the link goes
through `_link_native_mingw` (`--target=x86_64-w64-windows-gnu`). The runtime
objects are compiled with `--target=x86_64-w64-windows-gnu` only when the
target string ends in `-pc-windows-gnu`, so with an MSVC-default clang they are
MSVC-ABI objects (UCRT `__stdio_common_*`, `__chkstk`, `_fltused`) handed to a
MinGW link.

A GNU lane is not otherwise available on a Windows host either:
- explicit `--target x86_64-pc-windows-gnu` is refused by
  `hosted_c_compiler_plan` ("host C runtime/entry compilation unsupported");
- `SIMPLE_NATIVE_BUILD_TARGET=x86_64-pc-windows-gnu` without `--target` fails
  with "No C compiler found (hosted native link, target '')".

`MSYSTEM` -> `gnu` is coherent only when `CC` is a MinGW-default clang.

## Options

1. On a Windows host, ignore `MSYSTEM` for an unqualified target (default
   `msvc`; `SIMPLE_WINDOWS_ABI=gnu` / `SIMPLE_LINKER_FLAVOR=gnu` keep GNU).
2. Keep `MSYSTEM`, and compile the runtime and entry with
   `--target=x86_64-w64-windows-gnu` whenever the selected flavor is `gnu`,
   and admit the Windows-host GNU target in `hosted_c_compiler_plan`.

The bootstrap is unaffected: it always passes an ABI-qualified target.
