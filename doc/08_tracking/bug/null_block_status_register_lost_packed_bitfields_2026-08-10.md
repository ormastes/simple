# NullBlockStatusRegister lost its `@packed` bitfields in a file move (2026-08-10)

Status: **OPEN — spec left RED on purpose**
Found by: stream K4, while verifying comment-cheat anchor fixes

## Symptom

`NullBlockStatusRegister` is FR-DRIVER-0003's demonstration consumer of
`@packed` struct bitfields (`T:N` syntax). It is now declared with plain `u32`
fields and no `@packed` annotation:

```
src/lib/nogc_sync_mut/driver/null_block_driver.spl:14-17
struct NullBlockStatusRegister:
    ready: u32
    readonly: u32
    reserved: u32
```

Expected (what the spec asserts, and what the name implies):

```
@packed
struct NullBlockStatusRegister:
    ready: u32:1
    readonly: u32:1
    reserved: u32:30
```

As written it is three full 32-bit words, not a packed status register. The
parser-side feature is intact and separately tested — `fn_struct_decls.spl`
still parses `T:N` (`var fbits`, `parse_int_text`, and the "expected integer bit
width after ':'" error path) and `enum_module_body.spl` still consumes
`decl_get_field_bits`. What is gone is the only in-tree *user* of the feature,
so the end-to-end path has no coverage.

## Why it went unnoticed

`test/01_unit/compiler/packed_struct_bitfield_spec.spl` pointed at
`examples/09_embedded/simple_os/src/drivers/null_block.spl` — a path that does
not exist and has **no git history at all** (`git log -- <path>` is empty;
`examples/09_embedded/simple_os/` contains only `arch/` and `ref/`). The helper
returns `""` on a missing file, so the three assertions were failing against an
absent file, not against the product. The failure therefore read as "stale spec,
someone moved an example" rather than "the feature lost its only consumer", and
nobody chased it.

This is a distinct failure mode from the comment-cheat family: not a needle that
can never fail, but a needle that fails for a *misleading reason*, which is just
as effective at hiding the real defect.

## What changed

The spec now reads the real path
(`src/lib/nogc_sync_mut/driver/null_block_driver.spl`) and asserts, in order:
`struct NullBlockStatusRegister` (passes — the struct is there), then `@packed`
and `ready: u32:1` (both fail — the feature is gone). The failure now points at
the actual product file and the actual missing capability.

Left RED per `.claude/rules/testing.md`.

## Unblock condition

Restore the packed declaration in
`src/lib/nogc_sync_mut/driver/null_block_driver.spl:14`, keeping the field
semantics used by `null_block_status_register()` (`status.ready = 1` etc. must
still compile and read back correctly under bitfield widths). Verify with:

```
src/compiler_rust/target/bootstrap/simple test --timeout 900 \
  test/01_unit/compiler/packed_struct_bitfield_spec.spl
```

Both `test/01_unit/compiler/` and `test/unit/compiler/` copies of the spec must
be updated together — both trees execute.

Do not resolve by deleting the assertion or repointing it at a file that merely
mentions the struct name.
