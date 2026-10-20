# Trait-typed receiver whose implementor is in another unit lowers to a bare-name extern

`strategy.implementation_identity()` (pure_database.spl, `strategy` bound from
`Option<PureDatabaseBitmapReducerV1>`) reached codegen as a Call to the bare
name `implementation_identity`, not a virtual/trait dispatch. Cranelift and
LLVM both declared an `Import` of that bare symbol, and the link either bound
it to the FIRST same-named method in the closure (import_map "ambiguous pick
first") or fabricated a weak body returning nil.

## Status: fixed in the Rust seed (2026-10-20)

Measured red on the base seed with `test/native/cross_unit_trait_dispatch`
(trait + `Option<Trait>` calls in `ident.spl`, two `class X with Ident`
implementors in `main.spl`): both backends printed `alpha-2 alpha-impl-2`
for a `Beta` receiver — Beta's calls ran Alpha's body. With the fix both
backends match `expected_output.txt`; `missing/` fails to build on LLVM
(it already did) but still builds on Cranelift (see Still open); a
112-unit stdlib closure (io `with Read/Write/Close` classes, pure_sql
reducers) compiles identically before and after.

Root cause, two compounding gaps:

1. `class Name with Trait:` was never a trait implementation. The parser
   stores every `with` entry in `ClassDef.mixins`; HIR only honoured a real
   `mixin` declaration, so no `HirImpl`/vtable was recorded and
   `imports.rs` never put the class in `trait_impls`/`vtable_type_owners`.
   The trait therefore looked impl-less, `find_trait_for_method_on_receiver`
   returned the duck sentinel, and MIR fell back to a bare-name
   `MethodCallStatic`. (`impl Trait for X` and `struct X(Trait)` were fine.)
   Fix: `record_class_with_trait_impls` (module_pass.rs) and the matching
   `pending_class_with` resolution in imports.rs. A class lacking an abstract
   method keeps the old behaviour; imports.rs is deliberately the more
   permissive side so a disagreement fails the link (undefined vtable symbol)
   instead of producing a header-less object behind a virtual call.
   Only a class whose `with` clause names exactly ONE non-mixin entry, that
   has no explicit `impl Trait for` block, and that does not reach the trait
   through an import alias qualifies: an object has one vtable header and
   `MethodCallVirtual` carries only a slot number, so `with Read, Close` would
   call `read` for `close()` (Opus review). Multi-trait classes keep the old
   bare-name behaviour.
2. The payload of an `Option<Trait>` lost its declared trait:
   `type_name_hint`/`declared_trait_dispatch` have no `Type::Optional` arm and
   if-let / match payload bindings were plain locals. Fix: slot-keyed
   `FunctionContext.optional_trait_payloads` (params and annotated `val`s),
   carried to the if-let/while-let/match subject temp and given to the payload
   binding (`Some(x)`, or the bare identifier of `if val x = opt`) as its
   `trait_dispatch_owner`, so MIR emits `MethodCallVirtual` from the declared
   trait's slot table. Never stored on the optional local itself.

Stub policy: a bare trait-method name with no definition and no real alias
target is now an internal Simple symbol for `generate_stub_object`'s existing
fail-closed gate (refused unless `SIMPLE_ALLOW_INTERNAL_STUBS=1`; bootstrap,
`SIMPLE_NO_STUB_FALLBACK=1` and freestanding lanes unchanged -- the strict
lanes already leave it to the final link). It is defense-in-depth (LLVM's
bare-extern path, or an import_map target in a pruned module); no two-file
fixture reaches it.

## Still open

- An untyped (`Any`) receiver calling a method that several classes define,
  with no trait involved, still resolves through the bare `import_map` entry
  (first definition wins) when the calling unit's `use_map` has no candidates:
  `codegen/instr/closures_structs.rs` "Final fallback: import_map bare name"
  and the LLVM `self.import_map.get(method)` lookups in
  `codegen/llvm/functions.rs`. The `ambiguous_names` set is not threaded into
  `InstrContext`, so that fallback cannot refuse.
- Cranelift AOT still compiles an unresolved bare method call on an `Any`
  receiver to `rt_function_not_found` (prints, returns nil, exit 0); LLVM
  refuses it. Refusing it in Cranelift (tried in this lane) breaks
  `test_core_c_lane_simple_lsp_mcp_startup_initialize_reduced_source`:
  `self.store.list(...)` in
  `src/compiler/00.common/cache_contract/virtual_source_consumer_v1.spl`, a
  TRAIT-typed field (`store: VirtualSourceStoreV1`) whose impl is pruned from
  the entry closure, reaches codegen as a bare `list` on an `Any` receiver.
  Trait-typed FIELD receivers lose their trait the same way Option payloads
  did; fix that first, then make the Cranelift fallback an error.
  Fixture: `test/native/cross_unit_trait_dispatch/missing`.
- Multi-trait conformance (`class X with Read, Close`, or two `impl` blocks)
  needs per-(type, trait) vtables or a trait identity on `MethodCallVirtual`.
- A `mixin Foo` in one unit and a `trait Foo` used through `with` in another:
  HIR checks mixins locally, imports.rs project-wide. No such collision exists
  in the tree today.
