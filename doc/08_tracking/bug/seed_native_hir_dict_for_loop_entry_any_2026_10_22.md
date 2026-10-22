# Seed native HIR: dict for-loop entry typed ANY hard-fails field access

## Observed failure

Stage 2 (`--full-bootstrap --stop-after-stage2`, seed native pipeline
`SIMPLE_NATIVE_BUILD_RUST=1`) on release_phase3 @ bfcc3125bc8 failed with
exactly one file:

```
src/compiler/35.semantics/safety_checker_places.spl:
hir: Unsupported feature: cannot infer field type while lowering
safety_alias_join: struct 'ANY' field 'owner_id'
```

1483 files compiled; this was the sole failure (`failed=1`).

## Root cause

`TypeRegistry::get_iterable_element`
(`src/compiler_rust/compiler/src/hir/type_registry.rs:214`) has cases for
Array/String/Tuple/LabeledTuple but **no Dict case**, so
`for entry in some_dict` binds the loop variable as `TypeId::ANY`
(`hir/lower/stmt_lowering.rs:1054-1078`, tuple destructuring at :1081-1134
propagates the same ANY into both pattern bindings). Any field access on the
entry (`entry[1].owner_id`) is then field-access-on-ANY and the native HIR
pass hard-fails (`hir/lower/expr/access.rs:466`). The interpreter tolerates
the same source, so the defect is native-only, matching the class documented
in `doc/08_tracking/bug/native_dict_items_missing_lowering_2026_10_18.md`
(direct pair loops derive field types in the pure-Simple MIR producer, but
the Rust seed's HIR pass does not).

## Workaround (applied 2026-10-22)

`safety_alias_join` re-reads both aliases by key
(`first[entry[0]]` / `second[entry[0]]` into `val ... : SafetyClassAlias`)
before touching fields: typed dict index reads carry the value type, so
`.owner_id` / `.roots` resolve. Raw `entry[0]` indexing of the ANY entry is
tolerated by the lowering. Marked with a bug-linked `@workaround` comment in
`src/compiler/35.semantics/safety_checker_places.spl`.

## Proper repair (not done)

Add a Dict case to `get_iterable_element` returning a `(K, V)` entry type.
Caution: runtime dict iteration yields 2-element arrays
(`rt_dict_entries`, see `runtime_bridge.rs:279`), so the static entry type
must match the runtime representation the For codegen consumes — a naive
`Tuple[K, V]` risks an ABI mismatch. Needs a dedicated lane with both
backend evidence.

## Update 2026-10-22

The equivalent key-iteration repair landed as 83548ce08dd (PR #4121,
"robust safety_alias_join inference") with a TypeId-shift framing. This doc
retains the precise mechanism: `get_iterable_element` has no Dict case, so
dict for-loop entries lower as ANY and native HIR hard-fails field access.
Proper repair (not done): type dict iteration entries, matching the runtime's
2-element-array entry representation — see the original "Proper repair" note.
