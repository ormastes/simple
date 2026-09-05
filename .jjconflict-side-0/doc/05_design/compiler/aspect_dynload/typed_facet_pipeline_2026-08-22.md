<!-- codex-design -->
# Typed `facet<T>` Pipeline — Detail Design (2026-08-22)

## Scope and authority

This implements the typed-facet slice of Lane F after checked dynSMF pack
admission exists. Exact names and ownership come from
`doc/04_architecture/compiler/aspect_dynload/typed_facet_pipeline_2026-08-22.md`.
This design does not authorize transparent join-point patching or nominal
static introduction in the first implementation increment.

Registry locking, ACTIVE-last publication, stable single-flight attempts,
descriptor-coherent pack snapshots, generation tokens, and atomic retirement
follow `registry_transaction_2026-08-22.md`. Any older wording here about
independent activation cells or retirement queues is descriptive only.

## Pass sequence

1. Lexer recognizes no new generic-call syntax. Parser adds the declaration
   productions from design §6.1 and stores the four `ParserFacet*` collections,
   flattening the enclosing aspect ID/version onto each declaration.
2. Flat-AST assembly preserves source order, spans, attributes, pointcuts, and
   all four collections through cache encode/decode using flat tags 18–21.
3. HIR lowering defines facet symbols before bodies, resolves interface/base/
   implementation types, lowers method bodies, then resolves bindings.
4. `facet_resolution` computes stable IDs/hashes, validates completeness and
   uniqueness, and rewrites only resolved intrinsic calls to `FacetAcquire`.
5. MIR lowering emits acquire/invoke/release with cleanup on all normal/error
   exits. Escape/borrow checking prevents `FacetRef` outliving its base.
6. Pack emission serializes sorted binding descriptors and witness method rows.
   Catalog construction rejects duplicates and incomplete hash material.
7. Loader activation admits one exact route/module, stages a complete witness,
   and publishes one generation. Interpreter/native consumers dispatch through
   their mode-specific checked field.

Current `ApkFacetLoadV1` publication is not step 7: it returns payload bytes
before relocation or witness validation. Product code must not wrap it as a
`FacetRef` or claim typed activation from its `found` flag.

## Intrinsic resolution

A call is a facet acquisition only when all are true:

- method name is exactly `try_facet`, `facet`, or `require_facet`;
- one explicit type argument is present and no value arguments are present;
- the type argument resolves to `HirFacetInterfaceDecl`;
- the receiver has a concrete runtime type descriptor;
- normal member lookup did not resolve a user declaration with that name.

User methods win normal lookup; spelling alone is never rewritten. Diagnostics:
`E-FACET001` wrong arity, `E-FACET002` non-facet type argument,
`E-FACET003` unavailable concrete type identity, `E-FACET004` incomplete
implementation, `E-FACET005` ambiguous binding, `E-FACET006` forbidden
optional-business-interface extension, and `E-FACET007` inspect capability or
layout-hash requirement missing. The first increment diagnoses
`E-FACET008 UnsupportedNominalStatic`; it never silently lowers that mode as
`Attached`.

## Runtime interfaces

The loader exposes only typed facades:

```simple
fn facet_runtime_try<T>(ctx: FacetRuntimeContext, base: AnyRef,
    interface_id: FacetInterfaceId) -> Option<FacetRef<T>>

fn facet_runtime_acquire<T>(ctx: FacetRuntimeContext, base: AnyRef,
    interface_id: FacetInterfaceId,
    static_concrete_type_hint: ConcreteTypeId?,
    required: bool) -> Result<Option<FacetRef<T>>, FacetLoadError>

fn facet_runtime_invoke(ctx: FacetRuntimeContext, ref_: FacetRef<Any>,
    method_id: text, args: [Any]) -> Result<Any, FacetInvokeError>

fn facet_runtime_release(ctx: FacetRuntimeContext,
    pin: FacetGenerationPinV1) -> Result<(), FacetReleaseError>
```

`facet_runtime_try` consults only the published binding snapshot. Acquire uses
the context's already-open catalog bytes and selected profile; callers do not
pass arbitrary catalog bytes. `FacetRuntimeContext` binds:

```text
loader_id, catalog_bytes_owner, catalog_digest, profile_id,
capability_set, execution_mode, activation_cells,
published_generation_snapshot, sidecar_registry, retirement_queue
```

Catalog digest changes invalidate positive and negative route caches,
activation errors, and single-flight keys. It does not revoke already pinned
generations; policy must explicitly quiesce them.

Both facades authenticate `ConcreteTypeId` from `base`'s runtime descriptor. A
caller cannot provide or spoof the runtime lookup identity. `facet_runtime_try`
receives no static hint, so an optimization mismatch can never collapse an
integrity failure into clean absence. Loading acquire validates its optional
hint and returns `FacetLoadError.StaticTypeHintMismatch` on mismatch.

## Witness construction and calls

Stable hashes use domain-separated, length-framed fields, never prose
concatenation: `FacetInterfaceId = H("simple.facet.interface.v1", module_id,
aspect_id, aspect_version, name)`, `method_id =
H("simple.facet.method.v1", interface_id, method_name, canonical_signature)`,
and `binding_id = H("simple.facet.binding.v1", normalized FacetBindingPlan
fields)`. A detected collision is a hard diagnostic, never equality.

Method IDs follow that algorithm and rows
are sorted by method ID. Pack admission verifies unique IDs and exact method
coverage. The implementation hash covers provider identity, lowered method
closure, sidecar layout/factory, and required ABI hashes.

Interpreter hidden call arguments are `(base, sidecar, user_args...)` and route
through the existing interpreter function dispatcher by `callable_id`. Native
entries use the same logical signature but are invoked only by
`facet_native_abi.spl`; supported arities must be explicit. Unsupported arity
returns a typed error until a canonical aggregate-call ABI exists.

Every invocation revalidates that the pin's loader ID, facet key, and generation
match the ref's immutable witness owner. A mismatch returns
`FacetInvokeError.StaleGeneration` before touching sidecar or code.

The pack/catalog schema carries a typed `FacetBindingPlan` with `aspect_id`,
`facet_interface_id`, `facet_contract_abi_hash`, `target_type_rule`,
`facet_impl_id`, `access_policy`, `activation_mode`,
`required_core_public_abi_hash`, `required_core_layout_hash`,
`runtime_witness_abi_version`, and `variant_fingerprint`. It has no
`binding_plan_id`; that belongs only to join-point binding plans. Missing
expected ABI/hash material is malformed input, never "skip checking".

The witness export is `__simple_facet_witness_v1`, indexed by `facet_impl_id`.
Relocation and export resolution precede registry publication. Its method table
also carries optional generation-owned `state_factory` and `state_drop` hooks;
final unpin invokes `state_drop` before mappings retire.
Only `FacetMethodDescriptorV1(method_id, signature_hash, export_symbol)` is
serialized. Runtime `callable_id` and `native_address` are resolved after load
and never enter a pack, catalog, stable hash, or cache key.

## Transaction and recovery algorithm

```text
lookup published -> hit: pin and return
lookup activation cell -> wait or become owner
route catalog -> validate policy/capability/hashes
open exact pack -> recheck post-open digest -> admit exact module
stage mappings/relocations -> stage witness -> stage sidecar factory
lock publish owner -> recheck catalog generation and no competing binding
publish immutable generation -> acquire pin -> wake waiters
on failure: destroy staged sidecars -> remove witness -> undo relocations
            -> unmap staged owner -> clear activation cell -> wake typed error
```

Cancellation of the owner is a transient failure and executes rollback. Waiter
cancellation removes only that waiter. Permanent errors are cached against
catalog digest plus policy generation; transient errors are not sticky.

## Tests and frozen helper vocabulary

Executable specs belong under
`test/03_system/compiler/aspect_dynload/typed_facet_pipeline_spec.spl`; generated
manual output belongs under
`doc/06_spec/03_system/compiler/aspect_dynload/typed_facet_pipeline_spec.md`.
Unit tests may reuse the helpers below but must not rename or duplicate them.

Primary manual step text is frozen before parallel implementation:

```text
step("Compile a typed facet contract and binding")
step("Acquire an already resident facet without I/O")
step("Demand-load one admitted facet generation")
step("Invoke the facet through its typed reference")
step("Quiesce the generation while a reference remains pinned")
step("Release the final pin and reclaim the generation")
step("Reject an ambiguous or incompatible provider")
step("Recover cleanly after activation failure")
```

Canonical setup/checker helpers:

```simple
fn setup_facet_fixture() -> FacetFixture
fn setup_admitted_catalog(f: FacetFixture) -> FacetRuntimeContext
fn acquire_debuggable(ctx: FacetRuntimeContext, base: AnyRef) -> FacetAcquireObservation
fn check_no_io(observation: FacetAcquireObservation)
fn check_one_publication(observation: FacetAcquireObservation)
fn check_generation_pin(observation: FacetAcquireObservation)
fn check_rollback_clean(observation: FacetAcquireObservation)
fn check_typed_error(observation: FacetAcquireObservation, code: text)
fn sabotage_catalog_digest(f: FacetFixture) -> FacetFixture
fn sabotage_equal_rank_provider(f: FacetFixture) -> FacetFixture
```

Until an oracle calls production code and asserts its result, its body must be
exactly fail-closed, for example:

```simple
fn check_native_dispatch_is_real(observation: FacetAcquireObservation):
    assert(false) # FAIL-FAST: replace with mapped-call result and side effect

fn check_concurrent_single_flight_is_real(observation: FacetAcquireObservation):
    assert(false) # FAIL-FAST: requires real concurrent execution evidence
```

Never use `pass_todo`, empty bodies, `expect(true).to_equal(true)`, a fabricated
address, or an inline interpreter "thread" as acceptance evidence.

## Required test matrix

| Area | Required observations |
|---|---|
| grammar/cache | all four declarations, acquisition forms, malformed syntax, flat/HIR round-trip and stale-version miss |
| semantics | exact provider, generic provider, explicit selection, equal-rank ambiguity, incomplete methods, capability denial, require completeness |
| typing | exact three public result types, absence distinct from error, `FacetRef<T>` method surface, lifetime/escape rejection |
| catalog | direct route, no scan, profile isolation, duplicate route, ABI/interface/impl/layout hash rejects, post-open digest reject |
| activation | cold load, warm hit, clean absence, retryable failure, permanent error cache, rollback at each staged boundary |
| lifetime | clone adds pin, each drop removes one, quiescing refuses new pin, old call survives, final release, ABA stale-token reject |
| concurrency | one publication for N real callers, identical result, owner cancellation rollback, retry after transient failure |
| execution | interpreter callable dispatch and missing-callable error; native mapped dispatch, bad extent/signature/arity errors |
| invalidation | catalog digest/profile/policy generation invalidates the intended caches and leaves unrelated core/source caches reusable |

Every negative-control mutation must make its named test fail. The concurrency
row stays explicitly unavailable until the execution engine proves actual
parallel callers; sequential simulation cannot satisfy it.

For direct x86_64 native execution, `CallIndirect` must compile and execute a
real side effect with a signature-mismatch negative control. Until that passes,
the x86 typed-facet row is a hard failure/unsupported diagnostic, not fallback
through another backend.

## Performance and observability

Counters: catalog lookups, pack opens, bytes read/mapped, inflations,
activations owned/waited, generations published/retired, pin count, negative
cache hits, rollbacks, and dispatches by mode. Timers: resident acquisition,
cold activation, warm acquisition, and invocation p50/p95. No normal business
method pays a facet check; `try_facet` performs bounded in-memory lookup only.

The test fixture records catalog/artifact hashes and checksums. Loader tests
must show exactly one pack open and one module admission for a cold route and
zero I/O for resident lookup.

## Implementation stop gates

Do not claim the lane complete until generated artifacts are fresh, every
matrix row is real or explicitly unavailable, the fail-fast placeholders are
gone, native addresses come from admitted executable mappings, concurrency is
not simulated, and the existing aspect pack digest/pin/unload tests plus new
typed pipeline specs pass once after their final change.
