# `mir_module_canonical_fingerprint_v1` is not run-to-run stable for a type-defining module on the seed (2026-11-14)

Status: open. Found while writing
`test/01_unit/compiler/50.mir/mir_provider_symbol_relocation_retention_spec.spl`
(item 1 of `stage2_compiler_cli_build_mir_shard_share_unbounded_2026-11-06.md`).

## Symptom

Two knob-off lowerings of the same `lib.impl0` module (fresh HIR, same
closure, same order, seed `/home/yoon/dev/seed-try-target/release/simple`)
gave `simple/mir-fp/v1:c3812be7a699…` and `…:0d9b36b6d689…`; a third gave
`…:d833d12158e6…`. The serialized functions were byte-identical
(`serialize_mir_function` over `mir_module_functions_sorted`, 3 rows, `diff`
empty). Modules that define no types (`app.facade`, `app.user`) were stable.

## Mechanism

`src/compiler/50.mir/mir_canonical_fingerprint.spl:22`:

```
fn mir_fp_type_row(t: MirTypeDef) -> text:
    "{t.symbol.id}|{escape_json_string(t.name)}|{t.kind}|{t.is_export_c}|{escape_json_string(t.export_name)}"
```

`{t.kind}` stringifies `MirTypeDefKind::Struct([MirFieldDef(...)])` through the
runtime's struct Display, and the seed prints struct fields in hash order. The
same module printed, across runs:

```
MirFieldDef(offset: 0, name: side, type_: MirType(kind: MirTypeKind::I64), has_bits_attr: false, bits_width: 0)
MirFieldDef(type_: MirType(kind: MirTypeKind::I64), bits_width: 0, has_bits_attr: false, name: side, offset: 0)
MirFieldDef(type_: MirType(kind: MirTypeKind::I64), offset: 0, has_bits_attr: false, bits_width: 0, name: side)
```

Every other row of the fingerprint goes through the deterministic JSON
serializers (`serialize_mir_function`, `serialize_mir_type`,
`serialize_const_value`, `serialize_mir_enum_declaration_v1`).

## Consequence

The fingerprint's stated job (header comment: "cannot key a cache ... This
sorts every collection ... and covers all of them",
`native_cache_mir_fingerprint_prerequisite_blocked_2026-08-02.md`) does not
hold for any module with a `types` entry on the seed lane. Whether the native
lane's struct Display is field-order stable has not been measured here.

## Fix shape (not done here)

Render `t.kind` through an explicit serializer (field name, offset, type via
`serialize_mir_type`, bits attrs, in declaration order) instead of `{t.kind}`;
pin it with a spec that fingerprints one type-defining module twice from fresh
HIR and asserts equality. The retention spec above deliberately compares its
own deterministic row text instead of this fingerprint until then.
