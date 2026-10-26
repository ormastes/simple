<!-- codex-architecture -->
# Typed `facet<T>` Pipeline Architecture (2026-08-22)

## Status

Accepted implementation contract for Lane F of
`doc/03_plan/compiler/aspect_dynload/aspect_dynload_lane_plan_2026-08-19.md`.
It refines, rather than replaces,
`doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`.
No product option is selected here: the three public acquisition signatures,
explicit optionality, external witness representation, and generation pinning
were already fixed by that design.

The mutable registry, transaction, cache-coherence, and retirement authority is
`registry_transaction_2026-08-22.md`; this document does not authorize a second
`FacetRuntimeContext` activation table or retirement queue.

## Decision

Typed facets are one vertical pipeline with five owners:

1. `compiler.frontend` owns source grammar and parser declarations.
2. `compiler.hir` owns resolved facet identity and typed acquisition nodes.
3. `compiler.mir` owns explicit acquisition and invocation operations.
4. `common.facet_abi` owns passive, versioned cross-runtime records only.
5. `compiler.loader` owns catalog context, activation, witness publication,
   generation pins, native address validation, and retirement.

The interpreter and native backend are peer consumers of the same MIR and
`common.facet_abi` records. Neither may re-parse source, invent a second facet
registry, or call arbitrary catalog payload bytes as code.

```text
source
  -> ParserFacet* declarations + ordinary generic method-call syntax
  -> HirFacet* declarations + HirExprKind.FacetAcquire
  -> MirOp.FacetAcquire / MirOp.FacetInvoke / MirOp.FacetRelease
  -> FacetRuntimeContext
       -> catalog route -> checked module admission -> staged witness
       -> atomic FacetGeneration publication -> FacetRef<T> pin
       -> interpreter callable ID OR validated native entry address
```

This is a virtual capsule: the grammar, typed IR, metadata, and runtime adapter
form one feature, while ownership remains layered. Loader-private state never
moves into `00.common`; passive ABI records do.

## Exact compiler surface

### Frontend-owned declarations

Append these defaulted fields, in this order, to `ParserModule`, after every
existing field so Rust-seed positional construction remains valid:

```simple
facet_interfaces: [ParserFacetInterface] = []
facet_impls: [ParserFacetImpl] = []
facet_bindings: [ParserFacetBinding] = []
facet_requirements: [ParserFacetRequirement] = []
```

The declaration names and fields are normative:

```simple
struct ParserFacetInterface:
    aspect_id: text
    aspect_version: i64
    name: text
    type_params: [ParserTypeParam]
    composes: [Type]
    methods: Dict<text, ParserFunction>
    visibility: Visibility
    is_public: bool
    attributes: [Attribute]
    span: Span

enum ParserFacetAccessMode:
    PublicReadonly
    InspectReadonly

struct ParserFacetImpl:
    aspect_id: text
    aspect_version: i64
    name: text
    type_params: [ParserTypeParam]
    base_type: Type
    interfaces: [Type]
    access_mode: ParserFacetAccessMode
    methods: Dict<text, ParserFunction>
    attributes: [Attribute]
    span: Span

enum ParserFacetBindingMode:
    Attached
    NominalStatic

struct ParserFacetBinding:
    aspect_id: text
    aspect_version: i64
    interface_type: Type
    pointcut_text: text
    implementation_type: Type
    mode: ParserFacetBindingMode
    priority: i64
    provider_id: text
    span: Span

struct ParserFacetRequirement:
    aspect_id: text
    aspect_version: i64
    interface_type: Type
    pointcut_text: text
    span: Span
```

Surface `extends` lowers into internal `composes`. It means facet-contract
composition only: no implementation inheritance, nominal base conformance,
field addition, or layout mutation. Aspect nesting or manifest context
populates `aspect_id` and `aspect_version` on every flattened node;
`provider_id` identifies an implementation provider, not aspect ownership.

The acquisition spellings remain ordinary generic method-call syntax in the
frontend: `try_facet<T>()`, `facet<T>()`, and `require_facet<T>()`. Do not add
an AST expression fork. The semantic pass alone recognizes them after normal
method lookup has established that the callee is the intrinsic facet surface.

### HIR-owned declarations and expression

Append matching defaulted `HirModule` fields:

```simple
facet_interfaces: [HirFacetInterfaceDecl] = []
facet_impls: [HirFacetImplDecl] = []
facet_bindings: [HirFacetBindingDecl] = []
facet_requirements: [HirFacetRequirementDecl] = []
```

Canonical resolved types:

```simple
struct HirFacetMethod:
    symbol: SymbolId
    name: text
    function: HirFunction
    method_id: FacetMethodId
    signature_hash: text
    span: Span

struct HirFacetInterfaceDecl:
    aspect_id: AspectId
    aspect_version: i64
    symbol: SymbolId
    name: text
    type_params: [HirTypeParam]
    composes: [HirType]
    methods: [HirFacetMethod]
    visibility: Visibility
    is_public: bool
    attributes: [HirAttribute]
    interface_id: FacetInterfaceId
    interface_abi_hash: text
    span: Span

enum HirFacetAccessMode:
    PublicReadonly
    InspectReadonly

struct HirFacetImplDecl:
    aspect_id: AspectId
    aspect_version: i64
    symbol: SymbolId
    name: text
    type_params: [HirTypeParam]
    base_type: HirType
    interfaces: [HirType]
    access_mode: HirFacetAccessMode
    methods: [HirFacetMethod]
    provider_id: text
    implementation_hash: text
    required_base_abi_hash: text
    required_layout_hash: text
    span: Span

enum HirFacetBindingMode:
    Attached
    NominalStatic

struct HirFacetBindingDecl:
    aspect_id: AspectId
    aspect_version: i64
    interface_type: HirType
    target_type_rule: HirTypePointcut
    implementation_type: HirType
    mode: HirFacetBindingMode
    priority: i64
    provider_id: text
    binding_id: FacetBindingId
    span: Span

struct HirFacetRequirementDecl:
    aspect_id: AspectId
    aspect_version: i64
    interface_type: HirType
    target_type_rule: HirTypePointcut
    span: Span

enum HirFacetAcquireMode:
    TryResident
    LoadOptional
    LoadRequired
```

Add exactly one expression variant:

```simple
FacetAcquire(receiver: HirExpr,
             interface_type: HirType,
             interface_id: FacetInterfaceId,
             static_concrete_type_hint: ConcreteTypeId?,
             mode: HirFacetAcquireMode)
```

Resolved IDs are deterministic logical IDs, never absolute paths or process
addresses. `interface_id` is the fully qualified facet symbol plus declared
version. Runtime derives `ConcreteTypeId` from the base object's authenticated
runtime type descriptor. A static hint is optimization only and must equal the
descriptor before lookup; caller/HIR text never selects a witness for another
layout. The v1 wire key encodes the derived ID and interface ID behind checked
typed helpers.

Mode-specific lowering drops the hint for `TryResident`; `try_facet` derives
identity solely from the descriptor and cannot represent hint mismatch in its
`Option` result. Loading modes retain the hint and report
`FacetLoadError.StaticTypeHintMismatch` through `Result`.

### Generated tree machinery

The source definitions are authoritative; generated files are never hand
edited. The implementing lane must:

- teach `src/app/compiler_schema/visitor_gen.spl`, `fold_gen.spl`, and
  `codec_gen.spl` that the
  four appended module collections and all `HirFacet*` fields are reachable;
- regenerate `src/compiler/10.frontend/generated/ast_visitor.spl`,
  `src/compiler/20.hir/generated/hir_visit.spl`, `hir_visitor.spl`,
  `hir_children.spl`, `hir_hash.spl`, and `hir_codec.spl`;
- extend the flat AST module bridge/codec for the four parser collections;
- bump `FLAT_POOL_CODEC_VERSION` and `HIR_CODEC_VERSION`; an old cache is a
  miss, never a partial decode;
- run compiler-schema freshness, visitor completeness, flat-AST round-trip,
  and HIR round-trip gates once after the final schema change.

Visitors recurse through receiver/type/pointcut/method/type-parameter fields.
Hashes and codecs include IDs, modes, priority, and ABI hashes. Omitting a new
field is a release-blocking lossy-codec defect.

## Semantic resolution and ambiguity

`compiler.semantics.facet_resolution` is the only source-level resolver. Parser
`pointcut_text` is accepted only from existing `pc{...}` grammar and lowers to
dedicated `HirTypePointcut`, then normalized `ResolvedTypeRule`; arbitrary
runtime expressions are rejected. It
constructs `FacetCandidate` rows from enabled, admitted bindings and resolves
the tuple `(concrete_type_id, interface_id, aspect_profile_id)`.

Eligibility is evaluated before ranking:

1. the type pointcut matches the concrete type;
2. the implementation's base constraint is satisfied;
3. every interface method is implemented with an exact compatible signature;
4. access capability is permitted;
5. core ABI, interface ABI, implementation hash, and (for inspect mode) layout
   hash constraints are present and compatible.

Ranking is deterministic: explicit profile provider selection, then concrete
base match over generic match, then greater declared priority. Source order,
filesystem order, pack order, and load timing are never tie-breakers.

If two eligible candidates remain at equal rank, resolution returns
`FacetResolveError.AmbiguousBinding(interface_id, concrete_type_id,
provider_ids)`. Provider IDs are sorted in the diagnostic. Compilation fails
for closed-world/static bindings; catalog construction fails for deploy-time
bindings; runtime admission fails if a malicious or stale catalog recreates
the ambiguity. There is no "first wins" recovery.

`require facet` is checked against every known matching concrete type at link
time and against each newly admitted type descriptor before publication.

## Public type contract

The signatures are fixed:

```simple
obj.try_facet<T>() -> Option<FacetRef<T>>
obj.facet<T>() -> Result<Option<FacetRef<T>>, FacetLoadError>
obj.require_facet<T>() -> Result<FacetRef<T>, FacetLoadError>
```

Absence is `None`, never an error, for the first two calls. Loader, integrity,
policy, capability, ambiguity, ABI, or resource failures are `Err`; they must
not be collapsed to absence. `try_facet` performs no catalog read, file open,
mapping, decompression, relocation, or activation. `require_facet` converts a
clean absent result to `FacetLoadError.RequiredFacetMissing`.

`FacetRef<T>` is opaque to user construction and contains semantically:

```simple
struct FacetRef<T>:
    base: AnyRef
    base_pin: BaseObjectPinV1
    witness: FacetWitnessRef<T>
    sidecar: FacetSidecarHandleV1
    pin: FacetGenerationPinV1
```

It is not copyable. Construction takes a strong `BaseObjectPinV1`. Clone
acquires a new base pin and a new facet pin. Drop releases the facet pin first,
then the base pin; therefore method/sidecar use cannot outlive the object even
without source lifetime parameters. Calls borrow the ref so unload cannot race
a dispatch.

## Common ABI and runtime ownership

Create `src/lib/common/facet_abi.spl` as the stable passive-format owner:

```simple
val FACET_ABI_VERSION_V1: i64 = 1

struct FacetMethodDescriptorV1:
    method_id: FacetMethodId
    signature_hash: text
    export_symbol: text

struct FacetMethodEntryV1:
    descriptor: FacetMethodDescriptorV1
    callable_id: i64
    native_address: i64

struct FacetWitnessV1:
    abi_version: i64
    interface_id: FacetInterfaceId
    interface_abi_hash: text
    implementation_hash: text
    provider_id: text
    methods: [FacetMethodEntryV1]

struct FacetSidecarHandleV1:
    owner_generation: AspectGeneration
    opaque_id: i64

struct FacetGenerationPinV1:
    loader_id: i64
    binding_key: FacetBindingKey
    generation: AspectGeneration
    pin_id: i64

struct BaseObjectPinV1:
    object_id: i64
    pin_id: i64
```

Add typed wrappers `FacetInterfaceId`, `FacetMethodId`, `FacetBindingId`,
`ConcreteTypeId`, `AspectId`, `AspectGeneration`, and
`FacetBindingKey(concrete_type_id, facet_interface_id)`
in the same module. The current `"{type}/{facet}"` key remains only a v1 wire
encoding behind checked `facet_binding_key_encode_v1` and
`facet_binding_key_decode_v1`; typed code never splits arbitrary text. IDs must
reject `/` before v1 encoding.

Pack/catalog files serialize only `FacetMethodDescriptorV1`; process-local
callable IDs and relocated addresses exist only in runtime entries materialized
after witness resolution. Implementation hashes cover descriptors and code
identity, never addresses or session-local callable IDs.

Facet pin IDs are unique monotone loader-owned tokens. The registry keys a live
pin by `(loader_id, binding_key, generation, pin_id)`; release atomically
consumes that row. A repeated release returns `AlreadyReleased` without changing
the refcount, and clone allocates a new pin ID. Base pins follow the same
consume-once rule in the object owner.

These are values and identifiers, not owners of mappings or raw pointers.
`native_address` is zero in interpreter artifacts; `callable_id` is zero in a
native-only artifact. Mixed-mode artifacts may carry both only if both bind to
the same `method_id` and `signature_hash`.

`src/compiler/99.loader/facet_runtime.spl` is the sole mutable owner. Its
`FacetRuntimeContext` holds loader/catalog/profile/capability context,
single-flight activation state, immutable published generations, sidecar
owners, and retirement queues. It adapts the existing `apk_*` catalog and pin
operations; it does not duplicate them.

The existing `ApkFacetLoadV1` is explicitly **not** a `FacetRef`: it contains
admitted module payload bytes and route metadata, not a relocated witness,
callable method table, sidecar owner, or pin. `apk_*` remains container/admission
substrate. `AspectActivationManager.activate_facet(binding_key)`,
`FacetBindingRegistry.try_acquire(binding_key)`, and `AspectGenerationHandle`
form the new runtime layer. Activation loads and relocates the module, resolves
the versioned `__simple_facet_witness_v1` export indexed by implementation ID,
validates it, and only then publishes the registry generation.

`src/compiler/99.loader/facet_native_abi.spl` is the sole native call boundary.
It validates version, signature hash, mapped executable extent, W^X state, and
generation ownership before dispatch through canonical
`native_call_function_*` facades. No AST, HIR, interpreter, or facet library
module declares direct `rt_*` aliases or raw-address calls.

## Generation lifetime and unload

Activation stages catalog route, pack digest recheck, module admission,
relocations, witness table, and sidecar factory before one immutable
`FacetGeneration` is published. A successful acquisition atomically observes
one generation and obtains `ApkFacetPinV1` for that exact generation before it
can return `FacetRef<T>`.

Unload transitions `Bound -> Quiescing -> Released`:

- Quiescing refuses new acquisition and new pins.
- Existing `FacetRef` calls remain valid against their pinned generation.
- Final unpin destroys generation-owned sidecars, witness storage, and mappings
  in that order.
- Reload receives a new monotone generation. A stale pin can neither dispatch
  nor decrement the new generation (ABA protection).
- Process shutdown drains contexts through the same retirement path.

## Interpreter and native dispatch

MIR defines three operations:

```text
FacetAcquire(dst, receiver, interface_id, static_concrete_type_hint, mode)
FacetInvoke(dst, facet_ref, method_id, args) -> checked CallIndirect
FacetRelease(facet_ref)
```

Native lowering calls the loader-owned stable facade. Interpreter execution
calls `facet_runtime_acquire`, looks up `callable_id`, and invokes the normal
interpreter function dispatcher with `base` and `sidecar` as hidden leading
arguments. It never attempts to execute `native_address`. If an admitted
artifact has no interpreter callable, return
`FacetLoadError.ExecutionModeUnavailable`; do not fake success or reinterpret
bytes. Native dispatch symmetrically rejects a missing/invalid native address.

The x86_64 direct native selector currently rejects `CallIndirect`. Therefore
x86 typed-facet execution is not deliverable until that backend implements and
tests signature-checked indirect calls. Other backends are not evidence for
x86. Until then x86 compilation must reject the feature explicitly; it may not
substitute a direct call or fabricated address.

## Flat bootstrap representation

The rich parser model is not the bootstrap parser's only representation. Add
append-only flat declaration tags in
`src/compiler/10.frontend/core/_Ast/decl_nodes.spl` without renumbering any
existing tag:

```text
DECL_FACET_INTERFACE = 18
DECL_FACET_IMPL      = 19
DECL_FACET_BIND      = 20
DECL_FACET_REQUIRE   = 21
```

Each has dedicated parallel fields, constructors, and accessors; it must not be
encoded as `DECL_AOP_ADVICE`. Update flat module assembly, arena snapshot, and
environment codec together with the rich AST bridge. Existing tag numbers and
field order remain stable for Stage 3 seed consumers.

## Recovery contract

All activation work is transactional. Before publication, any failure rolls
back sidecars, witness entries, relocations, mappings, and single-flight state
in reverse ownership order. The prior published generation remains active.

Error classes and retry rules:

| Class | Examples | Retry |
|---|---|---|
| permanent artifact | digest, ABI, interface, impl hash, ambiguity | only after catalog/artifact identity changes |
| permanent policy | disabled mode, denied capability, forbidden inspect | only after context/policy generation changes |
| clean absence | no catalog route | returned as `None`; negative-cache by catalog digest |
| transient resource | bounded I/O interruption, temporary allocation | explicit later call may retry |
| execution mode | callable/address unavailable | only after compatible artifact admission |

Concurrent callers share one activation attempt per
`(catalog_digest, facet_key, target_generation)`. Waiters receive the identical
typed result. A failed attempt clears the in-flight cell only after rollback;
no caller may observe staged state.

TF-6 may not implement this with the current re-entrancy stack or inline
interpreter spawn. Before implementation it must select an existing proven
mutex/atomic once-cell primitive and name that owner in its handoff, then prove
real contention. If no such primitive is admitted, concurrent activation stays
fail-fast unavailable; sequential simulation cannot satisfy single-flight.

## Consequences

Positive: one grammar, one typed IR, one runtime registry, truthful absence vs
failure, unload-safe dispatch, cache fidelity, and backend parity.

Negative: adding four module collections requires deliberate codec migrations;
`FacetRef` is move/borrow sensitive; open-world activation remains unavailable
until real atomic single-flight and executable-dispatch evidence exists.

Neutral: catalog lookup remains keyed by text in v1 for compatibility; a future
interned ID optimization may preserve the exact logical identity contract.

## References

- `doc/03_plan/compiler/aspect_dynload/aspect_dynload_lane_plan_2026-08-19.md`
- `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`
- `src/lib/common/aspect_pack.spl`
- `src/compiler/10.frontend/parser_types.spl`
- `src/compiler/20.hir/hir_types.spl`
- `src/app/compiler_schema/{visitor_gen,fold_gen,codec_gen}.spl`
- `src/compiler/99.loader/{module_loader_compat,smf_mmap_native}.spl`
