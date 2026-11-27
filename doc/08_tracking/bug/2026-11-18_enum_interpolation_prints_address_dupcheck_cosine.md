# Enum interpolation prints an object address (id: dupcheck_enum_interpolation_erased_value)

Status: verification-pending (workaround landed; codegen defect open)
Bug ID: dupcheck_enum_interpolation_erased_value (shard doc/08_tracking/bug/db/dupcheck_enum_interpolation_erased_value.sdn, P2 open)

## Symptom
`"{token.kind}:{token.value}"` where `kind` is an enum field renders
`<enum@0x...>` under the seed interpreter and `<value:0x...>` under native
codegen: the raw erased value, i.e. a per-object address, not the variant name.
In `duplicate_check` cosine mode (`token_to_string` -> `build_feature_vector` ->
`feature_signature` -> bucket key) every key differs per object or collapses to
a few addresses, so buckets overflowed the cap (native 230 groups vs seed 43 on
`src/runtime`).

## Repro
```
enum K: A, B   # one variant per line
struct T: kind: K; value: text
print "{t.kind}:{t.value}"      # prints "<enum@0x..>:x"
```
Spec: `test/01_unit/compiler/tools/duplicate_token_key_spec.spl`.

## Workaround (tagged)
`token_kind_name` in `src/compiler/90.tools/duplicate_check/tokenizer.spl`.

## Open (real fix)
Text interpolation of a user enum value must call the enum's name/to_string
path in both the interpreter and native codegen instead of formatting the raw
erased value.

## Root-cause analysis (2026-11-18, fix NOT landed; deep)
Reproduced on the seed (`bin/simple.exe run`): `"{c}"`, `"{t.kind}"`, payload and unit variants all print `<enum@0x..>`.
The text comes from `value_to_display_string`, `HeapObjectType::Enum => format!("<enum@{ptr:p}>")`
(`src/compiler_rust/runtime/src/value/sffi/io_print.rs:777`). The heap enum is
`RuntimeEnum { enum_id: u32, discriminant: u32, payload }`
(`runtime/src/value/objects.rs:76`): no variant name is stored. `discriminant` is
the positional index (or a hash, `hash_variant_discriminant`, objects.rs:461)
and the only registry (`positional_registry`) maps name -> index, with no
`(enum_id, discriminant) -> name` reverse table, so the runtime cannot recover the name.
Real fix needs (1) an enum name table registered where enums are declared/lowered
(seed codegen `rt_enum_new` call sites, e.g. `codegen/instr/calls.rs:3175`, and the
pure-Simple native backend emitting the same table), (2) a lookup in `io_print.rs`.
Payload-variant text form still needs an owner decision (spec asserts prefix `Circle`).
Spec `test/01_unit/compiler/interp/enum_interpolation_text_spec.spl` (tagged
`@tag:in-development`) fails 3/3 on the seed. Workaround `token_kind_name` kept.
