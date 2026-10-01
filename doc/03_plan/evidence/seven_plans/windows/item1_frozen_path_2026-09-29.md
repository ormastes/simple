# Windows compiler frozen-path probe

Scope: seven-plan item 1, host-path parity at the existing public compiler
admission owner. Source: `src/app/compiler_entrypoint/admission.spl`.
Spec: `test/01_unit/app/compiler_entrypoint/frozen_path_spec.spl`.

The hypothesized failure was inconsistent handling of Windows verbatim path
prefixes between admission and frozen-path resolution. Existing snapshot code
already owns slash/prefix normalization through
`scv_compile_snapshot_plain_path_v1`; no alternative platform owner was added.

The initial test-first probe did **not** reproduce this failure. Unmodified
production source passed all three executed scenarios:

1. An existing repository source and the root map into the admitted snapshot.
2. An existing parent directory, invalid admission, and an empty path reject.
3. An already-frozen existing source remains unchanged through environment admission.

The exact Phase-1 seed used was
`C:/Users/User/dev/simple-bootstrap-main-windows/.simple/storage/build/bootstrap/stage3/x86_64-pc-windows-gnu/stage2-runtime-authority/simple.exe`.
Invocation: `test test/01_unit/app/compiler_entrypoint/frozen_path_spec.spl --mode=interpreter`.
Result: exit 0, declared/executed/passed 3, failed/skipped/dropped 0.
Log: `build/native_probe/item1-frozen-path/red.log` (filename retained; result is green).

A separate value probe printed the actual filesystem owner outputs:
`cwd`, `path_absolute(".")`, and `path_absolute` for an existing source all
returned ordinary `C:\Users\User\dev\simple-seven-plans-windows...` paths,
without a verbatim prefix. Its exit was 0; retained log:
`build/native_probe/item1-frozen-path/identity.log`.

Therefore the current Phase-1 interpreter cannot establish the claimed native
canonicalization regression. No production fix or export change was made on
this evidence. A real native Windows owner returning verbatim paths is still
needed for that claim. This is diagnostic regression coverage, not production
SPipe, self-hosted, native, or seven-item Windows/Linux completion evidence.
The passing suite was not rerun unchanged.

## Existing verbatim input criterion

A fourth scenario explicitly names the same existing source through its Windows
`\\?\C:\...` spelling. It first checks `file_exists(verbatim)`, then calls
`compiler_entrypoint_frozen_path_v1` and compares the exact snapshot path.
The expanded spec passed 4/4 without any production edits, exit 0, with four
declared/executed examples and no failures/skips/drops. Retained log:
`build/native_probe/item1-frozen-path/verbatim-red.log` (also green).
This proves the explicit input criterion under the diagnostic interpreter;
it does not show what a native runtime returns from canonicalization.
No production patch is justified by either observed result.

## Platform discovery correction

Review separated the fourth scenario into
`test/01_unit/app/compiler_entrypoint/frozen_path_windows_spec.spl` with
`# @platform: windows`. The first three remain in the portable common spec.
The scanner in `src/lib/nogc_sync_mut/test_runner/test_manifest_scanner.spl`
records this exact directive. `platform_tag_matches` in `test_runner_files.spl`
matches execution mode, not the host OS: ordinary interpreter/native/SMF
directory discovery excludes this Windows row on every host; a composite mode
matches it only if its specification contains `windows`. Direct single-file
invocation bypasses platform filtering, so this row must be invoked explicitly
on Windows and must not be directly invoked on Linux.

The passing verbatim assertion was moved without behavioral changes. No green
test was rerun for the file/metadata split. The retained four-example result
describes execution before that split, not automatic host-aware discovery.
