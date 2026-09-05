# Typed Facet Language Surface — Detail Design

**Status:** blocked design handoff; no source implementation claim  
**Architecture:**
`doc/04_architecture/compiler/aspect_dynload/typed_facet_witness_transaction_2026-08-26.md`

## Purpose

This document turns the witness/transaction architecture into exact compiler
and loader change points. It deliberately does not add a parser-only facade over
the current byte payload API.

## Source contract

```simple
obj.try_facet<T>()
obj.facet<T>()
obj.require_facet<T>()
```

All three require one type argument and zero value arguments. `T` must resolve
to one concrete, sealed `facet interface` instance. The exact types are:

| Source form | Type | Effect |
|---|---|---|
| `try_facet<T>()` | `Option<FacetRef<T>>` | resident registry only; no I/O/dynload |
| `facet<T>()` | `Result<Option<FacetRef<T>>, FacetLoadError>` | may dynload |
| `require_facet<T>()` | `Result<FacetRef<T>, FacetLoadError>` | may dynload; absence is error |

`FacetRef<T>` is opaque. User code cannot construct it, replace its vtable,
change its generation, access raw handles, or coerce `FacetRef<A>` to
`FacetRef<B>`. Ordinary `obj.facet()` remains an ordinary method call.

## Parser and AST changes

### Parser

Edit `src/compiler/10.frontend/core/parser_expr.spl` in postfix/member parsing.
After `.` and the member name:

1. For the exact names `try_facet`, `facet`, and `require_facet`, checkpoint the
   token stream when the next token is `<`.
2. Use the production type parser; do not parse a token slice or stringify it.
3. On successful type parsing, commit only when `>` is followed by `(`.
   Otherwise restore the checkpoint so `obj.facet < rhs` remains a comparison.
4. If type parsing fails but a `(` occurs before the current expression/line
   boundary, treat the sequence as an intended reserved call and emit the exact
   facet syntax error. Without such a call delimiter, restore the checkpoint.
5. Once committed, require exactly one type, `>`, `(`, and `)`. Reject commas,
   empty type arguments, and value arguments with `E-AF-TYPE-001`.
6. Construct a dedicated AST node with the full span from receiver start through
   `)`.

The generic lookahead at the bare-identifier call path must not consume and then
discard a facet type argument.

### Canonical AST

Append to `src/compiler/10.frontend/parser_types_expr.spl`:

```text
enum FacetAcquireModeAst { TryResident, LoadOptional, LoadRequired }
ExprKind.FacetAcquire(receiver: Expr, interface_type: Type,
                      mode: FacetAcquireModeAst)
```

Do not change the existing `MethodCall(Expr, text, [CallArg])` shape. Do not
encode `T` as a cast, dummy value argument, hidden identifier spelling, or text.

### Flat AST and generated transport

Add the corresponding flat node/tag and typed child in:

- `src/compiler/10.frontend/core/_AstExpr/nodes.spl`
- `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`

Regenerate or update exhaustive transport in:

- `src/compiler/10.frontend/generated/ast_semantic_value.spl`
- `src/compiler/10.frontend/generated/ast_visitor.spl`

The semantic-value encoder must preserve receiver, complete parsed type, mode,
and span. A round trip that drops or textualizes `T` is a failure.

## HIR and type-system changes

### Shared identity types

Add one Pure Simple owner, `src/lib/common/facet_identity.spl`, for
`FacetIdentityEncodingV1`, SHA-256 construction, NFC/path validation, canonical
recursive type encoding, and the distinct opaque four-`u64` newtypes defined by
the architecture. SHB, packer, HIR, MIR, and loader import those types; none
keeps a variable-length `[u8]` or text substitute. Only the owner can construct
an ID, and it rejects noncanonical inputs before hashing.

The facet-module compiler also produces `FacetImplAbiHashV1` from implementation
identity, state scope, access/layout contract, factory/destroy signatures, and
the ordered method/callable ABI set. Catalog V3, ModuleEntry V4, and witness
transport the same opaque value; loader admission recomputes and compares it.

### HIR schema

Append `HirFacetAcquireMode`, `HirFacetInterfaceRef`, and
`HirExprKind.FacetAcquire` as specified by the architecture in:

- `src/compiler/20.hir/hir_definitions.spl`

Append `FacetMethodResolutionV1` and
`MethodResolution.FacetMethod(FacetMethodResolutionV1)` in:

- `src/compiler/20.hir/hir_types.spl`
- `src/compiler/20.hir/__init__.spl`

Update every generated HIR surface:

- `src/compiler/20.hir/generated/hir_children.spl`
- `src/compiler/20.hir/generated/hir_codec.spl`
- `src/compiler/20.hir/generated/hir_hash.spl`
- `src/compiler/20.hir/generated/hir_visitor.spl`
- `src/compiler/20.hir/generated/hir_visit.spl`

Bump the serialized HIR schema/version so old caches cannot decode the new
variant as another expression. Hashing includes mode, symbol, instance type,
opaque interface ID, and opaque contract hash. The `MethodResolution` codec/hash
also preserves interface/method symbols, interface/contract/method/signature
identities, and slot.

### AST-to-HIR lowering

In `src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl`:

1. Lower the receiver once.
2. Resolve the AST type through normal type resolution.
3. Require a `facet interface` declaration, not an ordinary class or trait.
4. Instantiate all generic arguments and require a sealed ABI contract.
5. Read the interface ID and contract hash from admitted SHB/compiler metadata.
6. Build `HirFacetInterfaceRef` and the dedicated HIR expression.

No source/SHB file is reopened at expression-lowering time. The driver must
admit facet contract metadata once and provide it through the resolver/module
context.

### Inference and semantic passes

Add explicit inference in
`src/compiler/30.types/type_infer/inference_expr.spl`; do not route the node to
ordinary method-call inference, which can produce a fresh unconstrained result.
Construct exact `FacetRef<T>`, `Option`, and `Result` types from the admitted
core declarations.

All HIR exhaustive consumers must either handle `FacetAcquire` or deliberately
recurse into its receiver. At minimum audit/update:

- `src/compiler/30.types/type_infer/inference_effects.spl`
- `src/compiler/35.semantics/effect_validation.spl`
- `src/compiler/35.semantics/resolve.spl`
- `src/compiler/35.semantics/rt_criticality_validation.spl`
- `src/compiler/35.semantics/safety_checker_expr.spl`
- `src/compiler/35.semantics/visibility_integration.spl`
- `src/compiler/40.mono/monomorphize/hir_subst/body_subst.spl`
- `src/compiler/40.mono/monomorphize/type_subst.spl`
- `src/compiler/40.mono/verify/post_mono_verify.spl`

Every `MethodResolution` exhaustive consumer must add the facet case. The full
current source list is:

- `src/compiler/20.hir/generated/hir_codec.spl`
- `src/compiler/20.hir/hir_definitions.spl`
- `src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl`
- `src/compiler/20.hir/hir_lowering/_Expressions/match_desugaring.spl`
- `src/compiler/20.hir/hir_lowering/_Items/module_declarations_bootstrap.spl`
- `src/compiler/20.hir/hir_types.spl`
- `src/compiler/20.hir/__init__.spl`
- `src/compiler/20.hir/sffi_identity.spl`
- `src/compiler/30.types/type_infer/inference_expr_calls.spl`
- `src/compiler/35.semantics/perf_facts/collector.spl`
- `src/compiler/35.semantics/resolve_lookup_helpers.spl`
- `src/compiler/35.semantics/resolve.spl`
- `src/compiler/35.semantics/resolve_strategies.spl`
- `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`
- `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`
- `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`
- `src/compiler/50.mir/_MirLowering/module_lowering.spl`
- `src/compiler/70.backend/backend/interpreter_expr.spl`

Resolution of a method on `FacetRef<T>` looks up the admitted interface contract
once and produces `FacetMethodResolutionV1` with exact slot and opaque IDs/hashes.
An unresolved, ambiguous, stale-contract, or wrong-receiver result is a semantic
error; MIR never reconstructs this payload from a method name.
The HIR interpreter either dispatches `FacetMethod` through the explicit
execution-context loader, exact-generation guard, and validated vtable path, or
rejects it before evaluation with the stable unsupported-mode diagnostic. It
must never treat the payload as `InstanceMethod`, `TraitMethod`, or a direct
symbol call.

`TryResident` has no I/O/dynload effect. The other modes carry explicit dynload
and possible-I/O effects and must be rejected after seal or without capability.
Text scanning in `forbidden_io_context_scan` is not sufficient authority.

## MIR and facet method calls

Append these exact MIR types/variants rather than spelling loader function names
in user HIR:

```text
enum MirFacetAcquireModeV1:u8 {
    TryResident = 0, LoadOptional = 1, LoadRequired = 2
}

enum MirCallingConventionV1:u8 { TargetC = 1 }

struct MirFacetCallAbiV1 {
    interface_id: FacetInterfaceIdV1
    contract_abi_hash: FacetContractAbiHashV1
    method_id: FacetMethodIdV1
    signature_hash: FacetMethodSignatureHashV1
    calling_convention: MirCallingConventionV1
    pointer_width: u8
    ownership_bits: u64
    effect_bits: u64
    no_unwind: bool
}

MirInstKind.FacetAcquire(
    dest: LocalId,
    receiver: MirOperand,
    loader_context: MirOperand,
    interface_id: FacetInterfaceIdV1,
    contract_abi_hash: FacetContractAbiHashV1,
    mode: MirFacetAcquireModeV1,
    result_type: MirType
)

MirInstKind.FacetInvoke(
    dest: LocalId?,
    facet_ref: MirOperand,
    args: [MirOperand],
    slot: u32,
    call_abi: MirFacetCallAbiV1
)

MirInstKind.CallIndirectAbi(
    dest: LocalId?,
    ptr: MirOperand,
    args: [MirOperand],
    signature: MirSignature,
    call_abi: MirFacetCallAbiV1
)
```

`MirSignature` continues to carry parameter/result/variadic types for existing
APIs. `MirFacetCallAbiV1` is the missing non-optional ABI authority. Its bits use
the canonical facet-contract ownership/effect registry; unknown bits reject.
Effect bits are `IO=1<<0`, `ASYNC=1<<1`, `THROWS=1<<2`, `MUTATES=1<<3`, and
`ALLOCATES=1<<4`; `Pure` is zero and `Custom` is unsupported in V1. A declared
throw is normalized into the result ABI and never unwinds. Ownership uses
two-bit lanes in `ownership_bits`: lane 0 is hidden context, lanes 1..N are user
arguments, and lane N+1 is result; codes are `BORROWED_READONLY=0`,
`BORROWED_MUTABLE=1`, `MOVED_OWNED=2`, and `SHARED_REF=3`. V1 supports at most
30 user arguments so all lanes fit one `u64`.
Facet calls require `TargetC`, target pointer width, `no_unwind=true`, and
`MirSignature.is_variadic=false`. The verifier independently recomputes the
method signature hash from `MirSignature`, hidden `FacetCallContextV1`, target,
calling convention, ownership/effects, and unwind policy and compares it with
`call_abi.signature_hash`.

`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` lowers acquisition;
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` matches
`MethodResolution.FacetMethod` and emits `FacetInvoke` with its carried slot and
identities.
Post-monomorphization verification requires concrete opaque IDs, exact result
type, explicit loader-context operand, and a `MirFacetCallAbiV1` identical to its
`FacetMethodResolutionV1` and admitted contract.

The named elimination pass is
`src/compiler/50.mir/mir_facet_abi_lowering.spl::lower_facet_abi_ops`. It runs
after post-monomorphization facet verification and before every `60.mir_opt`
pass. `FacetAcquire` becomes exactly one of `rt_facet_try_resident_v1`,
`rt_facet_acquire_optional_v1`, or `rt_facet_acquire_required_v1` plus explicit
Result/Option control flow. `FacetInvoke` becomes:

1. validate the `FacetRef` control/public pin and acquire an exact-generation
   invocation guard;
2. load the loader-owned read-only vtable;
3. bounds-check the compile-time slot against the table's slot count;
4. compare the embedded interface/contract identity;
5. load the slot target;
6. emit `CallIndirectAbi` with the exact `MirSignature`, `MirFacetCallAbiV1`, and
   hidden `FacetCallContextV1`;
7. release the invocation guard on the normal/error return paths.

The same file provides `verify_no_high_level_facet_ops`, run immediately after
the pass. Any surviving `FacetAcquire`/`FacetInvoke` is a hard compiler error.
`CallIndirectAbi` remains through optimization and backend emission so its ABI
cannot be erased. Optimizers treat it as an opaque effectful call and preserve
its descriptor unless an independently verified facet-aware transform rewrites
both call and ABI proof.

Every current `CallIndirect` consumer must add `CallIndirectAbi` handling or an
explicit pre-emission unsupported diagnostic. This is the complete current
static inventory:

- core/serialization/verification:
  `src/compiler/10.frontend/core/mir.spl`,
  `src/compiler/50.mir/mir_aop_injection.spl`, `mir_data.spl`,
  `mir_instruction_kinds.spl`, `mir_json.spl`, `verification_ir.spl`,
  `verification_obligation_closure.spl`, `verification_obligation_module.spl`,
  `verification_region_effects.spl`, and `verification_semantic_coverage.spl`;
- optimization:
  `src/compiler/60.mir_opt/mir_opt/auto_vectorize_analysis.spl`,
  `_AutoVectorize/recipe.spl`, `auto_vectorize_validate.spl`,
  `collection_opt_core.spl`, `dce.spl`, `outline.spl`, `perf_facts.spl`,
  `storage_access_analysis.spl`, `var_reassign_analysis.spl`,
  `var_reassign_ssa.spl`, and `_OptimizationPasses/io_passes.spl`;
- backend/interpreter/driver:
  `src/compiler/70.backend/backend/_CBackendTranslate/instruction_lowering.spl`,
  `common/mir_text_codegen.spl`, `cranelift_codegen_adapter.spl`,
  `cranelift_gemm_fusion.spl`, `cuda_backend.spl`, `lean_mir_translate.spl`,
  `llvm_lib_translate_expr.spl`, `_MirToLlvm/aggregate_intrinsics.spl`,
  `_MirToLlvm/core_codegen.spl`, `lua_backend.spl`,
  `native/isel_riscv32.spl`, `native/isel_riscv64.spl`,
  `native/isel_x86_64.spl`, `opencl_backend.spl`, `vhdl_validation.spl`,
  `vhdl/vhdl_design_catalog.spl`, `wasm/wat_codegen.spl`,
  `src/compiler/80.driver/driver_source_pipeline_loading.spl`, and
  `src/compiler/95.interp/mir_interpreter.spl`.

No consumer may NOP, convert to ordinary `CallIndirect`, or discard the ABI
descriptor. LLVM/Cranelift/native/interpreter support must be explicit. Native
x86_64 currently rejects indirect calls, so it must implement the exact ABI or
reject facet-bearing code before instruction selection with a stable target
diagnostic.

## Loader change points

### Aspect pack

In `src/lib/common/aspect_pack.spl` add typed, fixed-ID Catalog V3 and
ModuleEntry V4 records plus a non-publishing immutable admission-lease API.
Preserve all V1/V2 compatibility records and calls. The typed path must reject the
existing permissive text key parser and must not call `apk_load_facet` because
that function publishes before mapping.

Prepared module selection returns an immutable payload and owner-bound
`ApkTypedFacetAdmissionLeaseV1`. The lease includes `FacetAdmissionProofV1` and
is transferred by the one committed loader-record insertion; there is no typed
aspect-pack commit or second registry mutation. The retained catalog index and
pack directory index are built at installation/admission, so a hot acquisition
performs no line scan.

Catalog installation first produces `ApplicationCatalogAdmissionProofV1` from
an application signature or independently pinned digest. `ModuleLoader` owns an
immutable out-of-band `FacetMinimumTrustPolicyV1`; route/catalog policy can only
strengthen it. A catalog-supplied trust root or downgrade is rejected.

### SMF metadata

Synchronize the proposed `.facet_witness` wire type in:

- `src/compiler/70.backend/linker/smf_writer.spl`
- `src/compiler/70.backend/linker/smf_reader.spl`
- `src/compiler/70.backend/linker/_SmfReaderMemory/**`
- the authoritative Rust SMF section enum/readers/writers
- `src/compiler/99.loader` validation helpers

The witness section includes the exact 320-byte binding, 80-byte method, and
80-byte callable ABI records, including state scope and all allowed flag bits.
The packer hashes the exact selected ordinary-SMF bytes and copies the hash to
the authenticated pack directory/catalog chain. Duplicate sections or mismatched
flag/metadata states fail closed.

### ModuleLoader

In `src/compiler/99.loader/module_loader_compat.spl`, add a private
reference-owned `ModuleLoadTransactionV1`, a fixed-ID committed binding registry,
and explicit execution-context entry points. Do not extend
`ModuleFacetRefV1` into the typed API; keep it as the compatibility payload pin.

The registry is a `TypedFacetRegistryOwnerV1` holding one immutable persistent
snapshot with both `next_generation` and tuple bindings. Commit allocates a
candidate snapshot, rechecks the old snapshot under the owner lock, and performs
one non-failing root-reference swap. It does not piecemeal-mutate the current
value-semantic loader dictionaries.

Refactor mapping through one staged owner using
`src/compiler/99.loader/segment_mapper.spl`. Mapping, relocation, symbol
resolution, protection, instruction-cache flush, witness validation, vtable
construction, and factory staging happen before publication. Existing global
symbol/module dictionaries are never used for typed facet exports: the staged
closure's private namespaces move inside the one committed binding record. The
only typed visibility mutation is insertion of that record into the tuple
registry.

The committed binding record is the only typed publication owner. It embeds the
immutable admission lease, mapping namespace, vtable, proof, state scope,
per-binding sidecar when applicable, and per-object instance map. Stateless and
per-binding factories run during activation. A per-object factory also uses a
binding-generation/object-identity single-flight for every later object; failure
destroys staged state before pinning, and `try_facet` fails closed to `None`.
Every later factory holds an exact-generation activation guard acquired while
`BOUND`; method calls hold invocation guards backed by an existing public pin.
Quiescing blocks new activation guards, and unload waits for all three counts.

The public runtime facade exports only opaque typed acquisition/release/call
handles. Raw map addresses, symbol indices, admission leases, and vtable slots
are private to the loader.

## Runtime data ownership

```text
ExecutionContext
  -> explicit ModuleLoader capability
     -> immutable FacetMinimumTrustPolicy + ApplicationCatalogAdmissionProof
     -> Dict<(ConcreteTypeId, FacetInterfaceId), CommittedFacetBinding>
        -> immutable AdmissionProof
        -> immutable admission lease + state_scope
        -> mapping owner + symbol namespace
        -> immutable FacetVTable
        -> optional per-binding sidecar
        -> Dict<(object identity, binding, generation), FacetInstanceControl>
        -> state + generation + public-pin/activation-guard/invocation-guard counts

FacetRef<T> shared control
  -> rooted base
  -> exact committed binding + generation pin
  -> shared sidecar instance
  -> immutable vtable
```

Acquisition and unload state transitions are:

```text
ABSENT -> PREPARING -> MAPPED -> SEALED -> STAGED -> BOUND
          |           |         |         |
          +-----------+---------+---------+-> ABORTED or QUARANTINED

BOUND -> QUIESCING -> UNLOADED
             |
             +-> QUARANTINED
```

Only `BOUND` is acquirable. `QUIESCING` refs already pinned remain callable.
`ABORTED`, `UNLOADED`, and `QUARANTINED` are never address-reused under the same
generation.

## Compatibility and migration

- Preserve `ApkFacetLoadV1`, `ModuleFacetRefV1`, text route functions, and
  existing catalog APIs.
- Mark them payload/compatibility surfaces in documentation; they never satisfy
  a typed-facet requirement.
- Do not reuse `src/lib/common/facet_syntax.spl` or `facet_registry.spl` as the
  compiler/runtime implementation. Their string registry model is separate.
- Source acceptance remains disabled until every prerequisite architecture item
  and all target backends in scope have an explicit implementation.

## Completion rule

The frontend lane may begin only after an xhigh static reviewer accepts this
contract or records specific changes. Landing parser syntax before the loader
transaction is prohibited because it would make an unsafe payload-only path look
like a language feature.
