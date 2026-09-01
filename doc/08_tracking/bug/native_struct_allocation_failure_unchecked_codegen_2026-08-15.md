# Native struct allocation failure is unchecked before generated stores

**Status:** FIX IMPLEMENTED — bootstrap activation and system verification pending
**Area:** Rust Cranelift / Rust LLVM / pure-Simple Cranelift object lowering

## Proven unsafe producers

- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`
  `compile_struct_init` calls `rt_struct_alloc` and immediately emits field or
  vtable stores. `emit_aggregate_block_copy` likewise allocates and then copies
  through the result.
- `src/compiler_rust/compiler/src/codegen/llvm/functions/objects.rs` has the
  equivalent struct-init and aggregate-copy paths. It validates the LLVM return
  value kind, but not whether the runtime pointer value is null.
- `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl` emits
  `rt_struct_alloc` for `Struct` and immediately emits field stores.
- No separate pure-Simple LLVM `rt_struct_alloc` call was found in the frozen
  sources; that absence must be re-audited when its object lowering changes.

The older retained native crash proved `rt_struct_alloc` returned null and
generated `HirLowering.lower_hir_expr` code wrote through it. Dynamically
growing the C registry removes the arbitrary 4,194,304-entry failure, but a
true allocator or address-space failure can still return null.

## Implemented fix

Both Rust object emitters now branch on a null `rt_struct_alloc` result before
the first vtable/field/copy store, emit the deterministic allocation-failure
diagnostic through `rt_panic`, and terminate with an unreachable/trap fallback.
The pure-Simple Cranelift struct constructor now performs the same null check,
diagnostic, and trap before its first field store. The source-contract spec
covers the two Rust paths plus the pure-Simple producer and passes 2/2; the
focused Rust LLVM-feature compile check also passes.

The code-level unchecked-store defect is fixed, but this record remains open
until a rebuilt authority emits the guards and a canonical Stage 3 transaction
either succeeds or terminates with the deterministic diagnostic rather than a
null-store SIGSEGV.
