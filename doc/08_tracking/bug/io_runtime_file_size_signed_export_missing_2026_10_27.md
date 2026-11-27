# `std.io_runtime` omits `file_size_signed` (2026-10-27)

Canonical bug ID: `io_runtime_file_size_signed_export_missing_2026_10_27`

## Evidence

The retained P2 all-object compile at
`D:/dev/simple-all-objects-phase2-20261027/build/object-campaign/bug-writer-build/compiler.log`
reports that `std.io_runtime` does not export `file_size_signed`, imported by
`std.nogc_sync_mut.io.process_ops` at line 811 and used at lines 1638, 1648, and
1687.

The implementation already exists as `pub fn file_size_signed` in
`src/lib/nogc_sync_mut/io_runtime.spl` and is exported by that owner at line 759.
The public `src/lib/io_runtime.spl` facade's explicit re-export list omitted it.

## Repair

The facade now explicitly re-exports `file_size_signed` from
`nogc_sync_mut.io_runtime`. This preserves the existing signed return contract:
positive size for a nonempty file, zero for an empty file, and a negative status
for an unreadable or missing file. No wrapper or alternate file-size function is
introduced.

## Regression coverage

`test/02_integration/io/io_runtime_file_size_signed_facade_spec.spl` imports
`file_size_signed` through `std.io_runtime` and calls the real function on an
existing source file and a unique missing path. It verifies positive and
negative results, rather than checking only for an export spelling in source.

## Qualification status

The pinned standalone API fixture passed HIR import resolution after this facade
export was added, then failed MIR lowering on shared library errors recorded in
`D:/dev/simple-object-repairs-luna-20261027/build/object-repair/file-size-api/run-entry/compiler.log`:

- `file_text_session.spl:122` and `:127` reject the `[u8]` `for-in` loops because
  MIR records the collections as `I64`.
- `external_text_io.spl` reports two `TextIoError.Codec` payload type mismatches.

No native executable was produced, so the fixture did not run. The facade export
is resolved through HIR, but native build and runtime qualification of the
positive and negative file-size results remain pending. The shared MIR errors
are tracked as separate source-workaround work; this record does not claim a
native compile or runtime pass.

Canonical bug database registration: PENDING. No canonical database mutation
has occurred; the native writer remains blocked by independent MIR failures.
