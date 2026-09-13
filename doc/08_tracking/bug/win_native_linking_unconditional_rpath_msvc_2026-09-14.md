# `_cc_fallback_runtime_lib_args` emitted `-rpath` unconditionally on Windows (2026-09-14)

## Symptom

`native_linking.spl`'s `_cc_fallback_runtime_lib_args` called
`native_runtime_archive_link_args(..., emit_rpath: true)` unconditionally, for
every host OS. On MSVC (`link.exe`) or when the cc-fallback path is reached
on a Windows host, the emitted `"-rpath"` `"<runtime_dir>"` pair is not a
recognized linker switch — MSVC's `link.exe` and lld-link's COFF driver treat
an unrecognized bare token as an input filename, so `<runtime_dir>` became
`<runtime_dir>.obj`, which does not exist, and the link failed (`LNK1181:
cannot open input file '<runtime_dir>.obj'`).

`-rpath` is an ELF/Mach-O runtime-search-path mechanism; PE/COFF has no
equivalent, so it must never be emitted for a Windows target regardless of
which flavor of linker (MSVC or mingw ld/lld) ultimately receives the argv.

## Why this path is reachable on Windows at all

`link_to_native` normally routes a Windows host straight to
`link_native_windows` / `_link_native_mingw` before ever reaching
`link_native_unix` → `link_native_cc` (the only caller of
`_cc_fallback_runtime_lib_args`). But that routing decision is itself made
from `host_os()`/`native_effective_link_os()` — the same detector proven, in
`doc/08_tracking/bug/win_host_os_detector_disagreement_2026-09-14.md`, to
have disagreed with a second implementation inside this exact Stage 2
bootstrap sanity harness. When the wrong detector answers "not Windows" on a
real Windows host, `os` falls through the Windows branch entirely and
`link_to_native` treats the host as Unix-like, reaching `link_native_cc` on
Windows for the first time. `_cc_fallback_runtime_lib_args`'s unconditional
`emit_rpath: true` then produces the bogus `-rpath` argument described above.

The host-OS-detector fix removes the *routing* bug, but
`_cc_fallback_runtime_lib_args` was still one detector-disagreement away from
reintroducing this exact failure (a future importer of a different `host_os`
implementation, a new call site, cross-compiling to Windows from a Windows
host, etc.), so it is fixed independently here as defense in depth, per this
file's own established pattern: every other Windows-vs-Unix branch in
`native_linking.spl` already reads `host_os()`/`native_effective_link_os()`
locally rather than assuming its caller's routing was correct.

## Fix

`_cc_fallback_runtime_lib_args` now computes
`emit_rpath = not native_linking_os_is_windows(host_os())` and passes that
through instead of a hardcoded `true`. `native_linking_os_is_windows` matches
every Windows `os` string this file already recognizes elsewhere
(`"windows"`, `"windows-msvc"`, `"windows-mingw"`), so the flag now tracks
the same effective-OS classification the rest of the file uses. The other two
call sites of `native_runtime_archive_link_args` were audited and left
unchanged: the direct-linker path in `link_native_unix` is only reached after
`link_to_native` has already routed a real Windows host to
`link_native_windows`/`_link_native_mingw`, and `native_msvc_runtime_selection`
already passed `emit_rpath: false` unconditionally.
