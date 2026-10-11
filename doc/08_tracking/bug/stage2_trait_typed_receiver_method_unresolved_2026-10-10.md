# Stage2: method call on a trait-typed value never resolves (no dynamic trait dispatch)

- Date: 2026-10-10
- Lane: link ladder, frozen stage2, `simple_lsp_mcp` build
- Symptom: `unresolved method call: list|stat|read|page` at
  `src/compiler/00.common/cache_contract/virtual_source_consumer_v1.spl:24-36`.

## Receiver

`VirtualSourceConsumerAdapterV1.store: VirtualSourceStoreV1`, and
`VirtualSourceStoreV1` is a `pub trait`
(`virtual_source_store_v1.spl:68`), i.e. a trait OBJECT field.
`self.store.list(...)` is a dynamic trait call. The only implementor is
`impl VirtualSourceStoreV1 for VirtualSourceStoreAdapterV1`
(`src/compiler/80.driver/cache/summary/summary_store_v1.spl:275`), which is not
in the `simple_lsp_mcp` import closure (that app reaches the leaf
`virtual_source_read_registry_v1.spl`, which takes an already-selected store).

## Why it does not resolve

`35.semantics/resolve_strategies.spl` `resolve_method` tries
`try_instance_method` (looks up the method in the receiver TYPE's method table:
a trait symbol has none) then `try_trait_method` (looks for traits the receiver
type IMPLEMENTS: a trait does not implement itself). No branch handles "the
receiver's static type IS a trait". MIR (`method_calls_literals.spl:4069`)
then reports `unresolved method call`.

Even with a `TraitMethod(trait, method)` resolution, MIR would emit a direct
call to the abstract trait method symbol (no body). Stage2 MIR has no vtable /
trait-object representation and lowers one module at a time
(`struct_method_syms` is built from the current module's `impls` only), so
cross-module dynamic dispatch needs a real design.

## Seed parity

The seed compiles this: it emits a vtable call when an `impl Trait for T` is in
the unit, and otherwise a `DUCK_DISPATCH_UNSUPPORTED_SLOT` trap
(`compiler_rust/compiler/src/codegen/instr/closures_structs.rs`
`compile_method_call_virtual`) that fails loudly only if the site runs.

## Fix options (owner decision)

1. Stage2 trait objects: box `(vtable, data)` at coercion sites, per-impl
   vtables, indirect call at trait-typed receivers. Full parity.
2. Seed-parity minimum: resolve a trait-typed receiver's method to
   `TraitMethod`, and in MIR lower it to a named `rt_panic` trap when no impl
   is visible (dead site), exactly like the seed's no-vtable sentinel.
3. Source workaround: replace the trait-object field with a concrete store
   type or fn-typed fields. Not applied: it would normalize the gap.
