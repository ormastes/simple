# A `T?` struct value stored into a desugared `has_x / x: T` field keeps the Option enum box (Stage 3 B7)

- **Date:** 2026-10-25
- **Status:** workaround in source (declaration_lowering.spl, class_declaration_lowering.spl); compiler fix OPEN
- **Severity:** P0 for Phase 3 Stage 3 (hello world SEGV in HIR encode, right after B6)
- **Producer:** Stage 2 (p2shard-17), Cranelift aarch64

## Symptom

With the B6 fix (private link `S/r27/bp/simple.p3b6x`), hello SEGVs in
`__strlen_asimd(x0=0x100000001)` <- `flat_pool_escape` <- `HirCodecWriter.put_text`
<- `hc_enc_export_attr` <- `hc_enc_hir_function` <- `hc_enc_hir_module`.

gdb at `hc_enc_export_attr`: the node is a 16-byte copy whose words are
`[0x4, 0x0000000100000001]`. That is an `RtCoreEnum` header
(`kind = RT_VALUE_HEAP_ENUM (4)`, `transient_scope_id = 0`, `enum_id = 1`,
`discriminant = 1`, i.e. Option None), copied as if it were an `ExportAttr`.
`export_name` is then the enum's `enum_id/discriminant` word.

## Root cause

`HirFunction.export_attr` (field 17, +136; encoder and producer layouts agree) holds
the Option box itself:

- `parse_export_attrs(..) -> ExportAttr?` returns `rt_enum_new(1, disc, payload)` on both
  paths (`return nil` -> None box, found -> Some box), seen in the disassembly at 0x332139c / 0x3321330.
- `declaration_lowering.spl` `export_attr: parsed_export_attr` (a `val parsed_export_attr: ExportAttr?`)
  stores that box into the desugared NON-optional `export_attr: ExportAttr` field with no unwrap.
  Readers (`hc_enc_hir_function`'s `val enc: ExportAttr = node.export_attr; if not enc.?`) expect
  a raw struct handle or nil.

Same shape: `driver_manifest_attr: driver_manifest` (same constructor) and
`HirClass.export_attr` in `class_declaration_lowering.spl`.

Stage 2 repro (src/app/zz_p3b6/r4a.spl, r4b.spl, compiled by `S/r27/stage2-simple`):

| form | none | some |
|---|---|---|
| `Holder(.., ea: parsed)` with `parsed: Ea?` | SEGV | (not reached) |
| `var h = Holder(.., ea: nil); if val p = parsed: h.ea = p` | 0 | 2 (correct) |

Compiler fix (open, not built): struct-construct / field-store lowering must unwrap an
Optional-typed operand going into a non-Optional field: store the payload for Some and nil
for None, as `if val` does.

The generated decoder has the same shape (`var f_export_attr: ExportAttr? = nil` ->
`HirClass(.., export_attr: f_export_attr)`, hir_codec.spl hc_dec_*), which matters on
HIR-cache HIT paths. Not touched here: generated file, and tb.sh runs with a cold cache.

## Workaround

Construct with `export_attr: nil` / `driver_manifest_attr: nil`, then
`if val p = opt: obj.field = p` (tagged
`@workaround bug=optional_struct_stored_into_desugared_field_keeps_option_box_2026-10-25`).
Regression spec: `test/01_unit/compiler/50.mir/optional_struct_into_desugared_field_spec.spl`.
