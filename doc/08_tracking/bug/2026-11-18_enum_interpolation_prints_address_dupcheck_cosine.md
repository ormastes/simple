# Enum interpolation prints an object address (id: dupcheck_enum_interpolation_erased_value)

Status: verification-pending (workaround landed; codegen defect open)

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
