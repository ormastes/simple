# Seed interpreter: integer dict keys come back as text from `keys()` / iteration (2026-10-30)

Status: open
Area: Rust seed interpreter, `src/compiler_rust/compiler/src/value_impl.rs` (dict entry helpers)
Found by: `test/01_unit/compiler/type_inference/generic_active_bound_inference_spec.spl`

## Symptom

Seed (`src/compiler_rust/target/release/simple`, built 2026-10-30 11:49) on
`release/1.0.0` @ `3e8daf44edb`:

```
bin/simple test test/01_unit/compiler/type_inference/generic_active_bound_inference_spec.spl
Results: 18 total, 17 passed, 1 failed
  refuses matching forwarding assumptions with a missing trait row
    semantic: array index out of bounds: index is 0 but length is 0
```

The example rebuilds a `Dict<i64, HirSymbol>` without one key:

```spl
var remaining: Dict<i64, HirSymbol> = {}
for key in module.symbols.symbols.keys():
    if key != trait_symbol.id.id: remaining[key] = module.symbols.symbols[key]
```

`keys()` returns `"7"`, not `7`, so `key != trait_symbol.id.id` is always true.
The trait row is never removed, and the expected "missing trait symbol" failure
never happens.

## Root cause

`Value::Dict` is `Arc<HashMap<String, Value>>`, keyed by `to_key_string()`.
Only composite keys keep their original value: `wrap_dict_entry` stores
`(__dict_entry__, key, value)`. Scalar keys (`dict_key_is_scalar`, including
`Int`/`UInt`) are stored bare. When code iterates without a key in hand
(`keys()`, `entries()`, `for k, v in d`), `dict_entry_key_for_iteration` falls
back to `Value::text(string_key)`. So an `i64` key comes back as text. The doc
comment on `dict_key_is_scalar` says `to_key_string()` is "a type-preserving
round trip" for these types. That is false for `Int`/`UInt` (and for
`Float`/`Bool`/`Nil`).

## Why this was not fixed in place

The obvious contained fix is to send `Int`/`UInt` keys through the existing
wrap path, by making `dict_key_is_scalar` false for them. Wrapping happens on
insert, so every reader of stored values has to unwrap. Many readers bypass the
helpers and read the map raw. There are about 170 `Value::Dict(` match sites in
39 non-test files, and only a handful call the unwrap helpers. Confirmed raw
readers that would start leaking `(__dict_entry__, k, v)` tuples for int-keyed
dicts:

- `interpreter_extern/sffi_dict.rs`: `rt_dict_values_fn` (returns raw stored
  values)
- `runtime_bridge.rs` `values_to_runtime_dict` (marshals stored values raw to
  the native runtime)
Related, though not a tuple leak: `rt_dict_keys_fn` returns raw string keys,
which is the same text-key defect as `keys()`. `rt_dict_get_fn` looks a key up
with `as_text_str()`, so it cannot read Int keys at all, either now or after
wrapping.

Not yet audited: `interpreter_module/module_loader.rs` (16 `Value::Dict(`
sites), `module_cache.rs` (12), `interpreter_call/*`, `value_bridge.rs`,
`di.rs`, and others. None of them call the helpers. Some may only build dicts
or handle module dicts keyed by text, but each one needs checking.

Composite-keyed dicts already have this latent leak today. Int-keyed dicts are
far more common: they hold the compiler's symbol tables, which the seed runs
during bootstrap. The change also adds a 3-element tuple per entry on that hot
path, so it needs a perf measurement. This is an audit of every raw reader plus
a bootstrap perf check, not a one-line seed fix.

## Fix direction

1. Route every raw `Value::Dict` value read through
   `unwrap_dict_entry` / `dict_entry_value_for_iteration`. Start with
   `sffi_dict.rs` and `runtime_bridge.rs`. A unit test with a struct-keyed dict
   pins the existing composite leak.
2. Then mark `Int`/`UInt` as non-scalar in `dict_key_is_scalar`, so `keys()`
   yields typed ints. Add a Rust unit test (`keys()[0] == Value::Int(42)`) and
   rerun the spec above.
3. Measure a stage-2 native-build (or `test/01_unit/compiler`) wall time and
   RSS before and after step 2.

Do not parse the string key back into an int in `dict_entry_key_for_iteration`.
`to_key_string()` maps Int `7` and text `"7"` to the same slot, so parsing back
cannot tell them apart. The wrap approach also leaves that collision.

A cheaper alternative needs a design decision: a typed key enum in place of
`String` in the backing map. That touches every `Value::Dict` site.

Side note: `dict_entries_sorted` orders by the string key, so int keys iterate
as `"10" < "9"`. Any fix that makes keys typed should decide whether that order
also changes.
