# SCV and rendering file-read byte contract

Pins the byte-level contract of the two canonical file-read entry points in
`src/lib/nogc_sync_mut/io/file_ops.spl` as unified on 2026-08-16:
`file_read_bytes` returns `[u8]`, `file_read_bytes_i64` returns the same bytes
as `[i64]`. SCV reads through the `[i64]` shape and narrows; the font and
rendering path reads `[u8]` directly. A return-type change to either entry point
silently reshapes every one of those readers.

Requirements: REQ-IOREAD-001 through REQ-IOREAD-006, defined in
`doc/03_plan/sys_test/scv_render_file_read_coverage.md`.

## stdlib file-read byte contract

### Writes a scratch fixture covering every byte value

1. Create the scratch directory and write bytes 0..255.
2. Confirm the fixture covers the full byte range.

### Should return unsigned bytes from the canonical read

1. Read the fixture through the canonical byte entry point.
2. Verify length is preserved.
3. Verify every element is a value in 0..255 at its written index.

### Should return the same bytes from the raw i64 read

1. Read the fixture through the raw i64 entry point.
2. Verify length is preserved.
3. Verify no element carries sign extension above 0x7F.

### Should agree between the unsigned and raw read shapes

1. Read the same fixture through both entry points.
2. Verify both shapes report the same length.
3. Verify both shapes report the same byte at every index.

## Rendering font read byte contract

### Requires the in-repo font asset

1. Confirm the font asset is present.

### Should preserve the sfnt version bytes of a real font

1. Read the font asset as bytes.
2. Verify the read returned a non-empty font body.
3. Verify the leading sfnt version bytes are `00 01 00 00`.

## Text and byte read agreement

### Should report the same ASCII content through both read families

1. Write a known ASCII payload.
2. Read it through the text family.
3. Read it through the byte family.
4. Verify the two families agree on length and content.

## Execution status

**These scenarios have not been executed.** They were authored while no
qualified pure-Simple runtime was available in the workspace: the Rust seed is
not admissible as evidence, and the on-disk bootstrap stages segfault on a
two-line program (see
`doc/08_tracking/bug/origin_main_seed_unbuildable_duplicate_heap_counter_symbols_2026-08-16.md`).

The specification is fail-closed by construction — every precondition is
asserted rather than assumed, no scenario skips, and no oracle is stubbed to
pass — so it cannot report green in an environment that does not satisfy the
contract. It is designed to run unchanged once a qualified runtime exists. No
pass may be claimed for it until it has actually run.

## Limitations

This evidence covers byte fidelity of the read entry points only. It does not
assert that the several same-named `file_read_bytes` definitions across the tree
agree with one another — that remains a static definition-count concern, tracked
in `doc/08_tracking/bug/file_read_has_23_definitions_with_two_return_types_2026-08-16.md`
and guarded by
`test/01_unit/lib/nogc_sync_mut/file_read_bytes_single_definition_spec.spl`.
It makes no claim about SCV pack, delta, or integrity semantics.
