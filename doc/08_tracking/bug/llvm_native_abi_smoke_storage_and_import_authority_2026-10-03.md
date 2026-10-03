# LLVM native ABI smoke blocked by storage and imported declaration authority

Status: source-reviewed, unresolved; no native execution attempted.
Scope: inspected pure-Simple HIR/MIR/LLVM paths on the item-3 ABI branch.

The requested smoke must import the canonical raw LLVM owner, call
LLVMGetVersion with three distinct local u32 output slots, require literal
23.1.1, obtain a non-null LLVMContextCreate result, and dispose that context.
It must link LLVM-C.lib through explicit BuildConfig declarations and report
success only after real native execution. Neither a context-only fixture nor
a same-file declaration fixture satisfies this acceptance criterion.

## Local address-of does not provide C output storage

`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:4261` recognizes Ref and
RefMut. Its local path at 4291 emits MirInstKind.Ref with the operand's value
type. `src/compiler/50.mir/mir_data.spl`, MirBuilder.emit_ref, allocates a result
local of that same type; it does not allocate writable storage for the referent.

`src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl:712`,
llvm_ref_impl, explicitly treats a borrow as identity on the place value. A
u32 local becomes `add i32 <value>, 0`, not an alloca address. The inspected
direct call and SSA transformation paths do not supply an output-pointer
storage/writeback bridge. Consequently `LLVMGetVersion(&mut major, &mut minor,
&mut patch)` is not proven to pass three writable unsigned-int addresses;
changing the declaration to ptr cannot create storage or writeback.

Existing pointer truth conditions do have LLVM null comparison lowering
(core_codegen.spl, conditional terminator's `icmp ne ptr ..., null`). That
does not fix local output storage. Casting local integer values to pointers,
using tagged nil as null, or substituting global mutable slots would not prove
the requested local-storage contract and was not introduced.

Required repair acceptance:

- Actual source with three local u32 variables and `&mut` call arguments lowers
  to three correctly sized/aligned writable locations, with addresses live
  throughout the call and post-call reads from those same locations.
- LLVM contains real address/storage operations rather than borrowed integer
  identities coerced to pointers. The repair distinguishes raw pointer output
  parameters from ordinary reference/value semantics.
- Cover aliasing two outputs to one permitted slot, independent slots, local
  reassignment before/after the call, and immutable/local-type rejection.
- On the admitted native runner, LLVMGetVersion yields exactly 23/1/1; context
  creation is non-null and disposal executes once. A changed version oracle
  must fail. Record the actual loaded provider identity and execution exit.

## Imported free extern authority is not propagated

`src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl:687`
materializes an imported callable type and defines a caller-local Function
symbol at 703 with defining-module provenance. It preserves/qualifies the
physical name at 716-718. The inspected free-function import branch does not
copy the provider HirFunction into the caller's module.functions.

The new exact_extern_signatures registry in
`src/compiler/50.mir/_MirLowering/module_lowering.spl` is seeded from local
HirFunction declarations only. Its provider loop handles relocated class
methods, not imported free extern declarations. Thus an actual imported raw
LLVM call can resolve to a caller-local symbol absent from this registry and
retain the legacy unknown parameter signature. The existing tests append a
caller to raw-owner source; they prove same-module declarations only.

Required repair acceptance:

- Parse/lower separate provider and consumer modules with a real selective
  import of LLVMGetVersion and LLVMContextCreate; require exact fixed MIR and
  LLVM call/declaration signatures in the consumer.
- Relocate declaration authority through the existing import owner metadata,
  checking actual is_extern provenance, source name, signature and caller-local
  symbol. Do not use a name whitelist or provider numeric SymbolId directly.
- Cover an aliased import, two modules reusing numeric IDs, a user function
  with the same spelling, missing provider evidence, and module reuse/reset.
- Preserve authority in the relevant module surface/cache representation and
  ordinary/flat/lifted-lambda lowering paths; unknown evidence stays unknown.

No additional compiler repair cycle was started in this slice. The raw owner
remains explicitly unsafe and unqualified for the broader native smoke. Safe
ORC provider/session lifetime and scalar invocation remain separate unfinished
work. This diagnosis does not claim every backend/import mechanism was audited.
