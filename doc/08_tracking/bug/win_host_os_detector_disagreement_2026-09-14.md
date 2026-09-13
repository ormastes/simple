# Windows host-OS detector disagreement — root cause and fix (2026-09-14)

## Symptom

During Windows Stage 2 bootstrap sanity harness in-process native-builds, four
independent, separately-landed fixes each found the same pattern: one call
site correctly detected the host as `"windows"`, while another call site, in
the *same process*, on the *same real Windows host*, detected `"not
windows"`:

- `#941` (`work/win-native-link-cc`): `io_compat.spl`'s `backend_shell_tuple`
  and `runtime_compiler.spl`'s `_find_c_compiler_windows` gate.
- `#944` (`work/win-native-link-libargs`): `native_linking.spl`'s
  `_cc_fallback_runtime_lib_args` / `native_runtime_archive_link_args` os
  branch.
- `#945` (`work/win-mir-target-triple`, merged):
  `mir_target_context_provider.spl`'s `backend_mir_target_context`.
- `#947` (`work/win-llvm-target-triple`): `llvm_target.spl`'s
  `LlvmTargetTriple.from_target_with_mode` hosted branch.

Each was fixed the same way: switch the call site's import from
`std.platform.{host_os}` (→ `nogc_sync_mut/platform.spl` →
`std.nogc_sync_mut.env.platform.is_windows_env`/`detect_os`) to
`std.io_runtime.{host_os}`, which answered `"windows"` correctly in every
traced incident.

## Root cause

`rt_platform_name` — the in-process runtime primitive both detectors
ultimately consult — was declared with **five independent, differing
`extern fn` signatures** across the tree:

| File | Signature |
|---|---|
| `src/lib/nogc_sync_mut/sffi/platform.spl` | `-> text` |
| `src/lib/nogc_sync_mut/fs/host_path.spl` | `-> text` |
| `src/lib/nogc_sync_mut/env/types.spl` | `-> text` |
| `src/lib/nogc_sync_mut/io_runtime.spl` | `-> text?` |
| `src/lib/sys/pty.spl` | `-> text?` |

Both the Rust (`runtime/src/value/sffi/env_process.rs::rt_platform_name`) and
C (`src/runtime/runtime_native.c::rt_platform_name`) implementations always
return a real string — never null — so the `-> text?` declarations were
already wrong relative to the real ABI, and the tree carried two
*disagreeing* nullability contracts for the same runtime symbol.

This is the exact defect class this repo's own compiler already warns about
for other symbols in the same build (`file_read_text_at`, `join_path`,
`mcdc_condition_key`): "N co-compiled definitions with N differing
signatures ... JIT call sites resolve by exact arg-type match ... falling
back to the last definition when types are ambiguous — a fallback hit may
still dispatch to the wrong one." When enough modules importing different
`rt_platform_name` declarations are co-compiled into one process — as
happens inside the Stage 2 bootstrap sanity harness's in-process
native-build, which pulls in a much wider module set than a plain `simple
run` of one file — a call site can silently dispatch through the wrong
extern registration, corrupting the returned value (or its `Optional`
unwrapping) at that call site only. That explains why the disagreement was
real, live, and reproducible in-process, but did not reproduce under a
plain fresh-process `simple run` of a small probe script that imports only
one detector at a time.

## Fix

Consolidated onto the single declaration in
`src/lib/nogc_sync_mut/sffi/platform.spl` (`platform_name_raw()`, `-> text`,
matching the real Rust/C ABI). Every other file that used to declare its own
`extern fn rt_platform_name` now imports `platform_name_raw` from
`std.sffi.platform` instead:

- `src/lib/nogc_sync_mut/fs/host_path.spl` — `_host_platform_name()`
- `src/lib/nogc_sync_mut/env/types.spl` — dropped the extern + export
  entirely (nothing outside `system_location.spl` imported it)
- `src/lib/nogc_sync_mut/env/system_location.spl` — updated its import
  accordingly
- `src/lib/nogc_sync_mut/io_runtime.spl` — `platform_name()`
- `src/lib/sys/pty.spl` — `platform_default_shell()`

`std.nogc_sync_mut.env.platform.detect_os()` (already fixed 2026-09-02 to
consult `platform_name_raw()` first) and `std.io_runtime.host_os()` now read
the *same* extern declaration, so they cannot disagree on the ABI level
again. POSIX fallback logic (env-var + `uname -s`) in every file is
unchanged.

This does not make the four per-call-site PRs (`#941`, `#944`, `#945`,
`#947`) redundant to revert — those PRs correctly moved their specific call
sites onto the proven-good `std.io_runtime.host_os()`, and that remains
correct regardless of this fix. What this fix removes is the *need* for a
fifth (and future) per-call-site patch: the 14 other importers of
`std.platform.{host_os, ...}` in `70.backend`/`80.driver` no longer need
individual migration, because the detector they already call
(`std.platform.host_os` → `detect_os()`) now shares one unambiguous
`rt_platform_name` ABI with `std.io_runtime.host_os()`.

## Verification

`test/01_unit/lib/nogc_sync_mut/host_os_detector_agreement_spec.spl` pins the
invariant that every public host-OS resolver
(`std.io_runtime.host_os`/`platform_name`, `std.platform.host_os`,
`std.nogc_sync_mut.env.platform.detect_os`/`is_windows`,
`std.sffi.platform.platform_name_raw`) agrees with every other one,
in-process. Manually verified on a real Windows host (`bin/release/x86_64-pc-windows-msvc/simple.exe run`,
a standalone probe importing all five resolvers together): every resolver
answered `"windows"`.
