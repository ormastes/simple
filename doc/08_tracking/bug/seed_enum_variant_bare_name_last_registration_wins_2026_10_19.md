# Seed resolves enum variants by bare enum name; the last registered enum wins

- Status: open (worked around for `ByteOrder` by rename on work/codec-native-build-and-perf)
- Severity: P1 — breaks every `native-build` that imports `std.io_runtime`
- Found: 2026-10-19, lane work/codec-native-build-and-perf

## Symptom

```
error: semantic: unknown variant or method 'NotApplicable' on enum ByteOrder
```

Raised at `src/lib/nogc_sync_mut/io/text_session.spl:71`
(`utf8_text_session_codec`) by any program that loads `std.common.binary_io`
after `std.io_runtime`. `native-build` always does: the interpreted driver
(shb reader/writer, linker inspectors) imports `binary_io`.

Two-line interpreter reproducer:

```
use std.io_runtime.{file_write, file_read}
use std.common.binary_io.{ByteOrder}
```

## Cause

Two modules declared `enum ByteOrder` with different variants:
`std.common.encoding.external_text` (NotApplicable, LittleEndian, BigEndian)
and `std.common.binary_io` (LittleEndian, BigEndian, Native). The seed looks up
the enum by its bare name, not by owning module, and the last registration wins:

- interpreter: `src/compiler_rust/compiler/src/interpreter_method/mod.rs:1375`
  (`enums` map keyed by name, `unknown_enum_variant_or_method`)
- MIR lowering: `src/compiler_rust/compiler/src/mir/lower/lowering_expr_ident.rs`
  (`enum_declares_variant(enum_name, …)`) and `lowering_expr_call.rs:663`

The leak is also visible in string interpolation: a spec that never imported
`ByteOrder` interpolated `"{ByteOrder}"` to `<enum:ByteOrder>`.

## Workaround landed

The codec enum was renamed `TextByteOrder` (commit "fix(codec): rename external_text ByteOrder -> TextByteOrder"). Regression:
`test/03_system/compiler/text_byte_order_enum_collision_spec.spl` with fixture
`test/fixtures/native_text_byte_order_collision/main.spl`.

## Still open

Any duplicate enum name can hit this again. A live latent case:
`Encoding` is declared in `std.common.encoding.external_text` (Utf8, Utf16,
Unknown) and in `std.common.encoding.codec` (Utf8, Utf16LE, …). Loading
`codec` after `external_text` would break `Encoding.Utf16`.

## Fix direction

Key enum lookup by the owning module (the import binding in the caller's
environment), not the bare name, in both the interpreter and MIR lowering. Until
then, also check the pure-Simple compiler's enum tables for the same keying.
