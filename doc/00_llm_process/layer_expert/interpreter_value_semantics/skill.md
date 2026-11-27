# Layer Expert: Interpreter Value Semantics

## Boundary rule

The AST/tree interpreter owns `Value`-level execution. A typed unsigned literal
that renders correctly but compares incorrectly has already crossed the parser
and literal-construction boundary intact; repair the `Value` operator owner,
not pure-Simple HIR/MIR lowering or the native runtime.

For integer ordering, use the shared unsigned-aware helper in
`src/compiler_rust/compiler/src/interpreter/expr/ops.rs`. `Value::as_int()` is
appropriate for bit-pattern operations but is not an ordering conversion for
`Value::UInt`. Keep relation operators symmetric and cover mixed signed values.

## Review checks

- Verify direct literals and struct fields preserve unsigned rendering.
- Exercise the failing value through its full container/Option boundary, not
  only through the comparison helper.
- Cover the sign edge and maximum: `2^63 - 1`, `2^63`, `2^63 + 1`, `u64::MAX`.
- A Rust-seed run is diagnostic evidence for this Rust-owned interpreter only;
  it is not a production pure-Simple or Stage 4 admission claim.

## Class identity is owner-exact (2026-11-27)

Owner decision: a class is identified by its OWNER module, not its bare name;
`use m.{Thing as Legacy}` and `m.Thing` name the owner-qualified class. Two
same-named classes get the owner-exact symbol `flatten_owner_mangled_name`
(`__spl_flat_<stem>_<hex>__Thing`) in every lane:

- flattened unit (run / JIT): `flatten_struct_owner.rs` census +
  `qualify_items_in_place`, shared by HIR and `evaluate_module_items`;
- lazily loaded module (test lane `load_and_merge_module`): the SECOND owner
  of a name registers under that symbol (`lazy_class_identity`), importer
  tables merge it under `class_slot_key`, never over the bare slot.

Instances carry the identity; `resolve_class_for_instance` matches a mangled
name exactly and never hands a bare-named instance a mangled def. Display
strips it (`flatten_owner_source_name`). Known gap: an entry module with two
LAZY same-named classes still errors `ambiguous type` (entry has no owner
bindings) -- loud, not a wrong dispatch.

Patterns, typed arms and class-typed params compare through
`class_identity_matches` (`module_cache.rs`): a bare identity of a shared name
matches only when the scope resolves the name to the bare class. Known gaps
(filed 2026-11-27): JIT struct patterns ignore owner identity
(`jit_pattern_same_name_class_identity_unchecked_2026_11_27`); the no-scope
fallback accepts by source name
(`interpreter_class_identity_no_scope_fallback_fail_open_2026_11_27`).
