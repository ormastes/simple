<!-- codex-design -->
# Architecture: Aspect Facets and Demand-Loaded SFM Packs

## Decision

Optional facet semantics are a structural extension of existing compile-time AOP, while deployment is an SFM capsule concern. The architecture adds no parallel SMF format, module loader, dynSMF lifecycle, variant resolver, or raw runtime I/O path.

```sdn
architecture:
  build:
    syntax: compiler.10_frontend
    coherence: compiler.20_35_semantics
    predicate: compiler.00_common.TypePredicateBytecode
    weave: compiler.50_mir + compiler.85_mdsoc
    package: compiler.80_driver -> std.sfm
  runtime:
    catalog: application_sfm.AspectCatalog
    provider: loader.ObjectProvider <- AspectPackProvider
    payload: opaque_ordinary_smf
    lifecycle: DynSmfSession + loader_generation
    publication: one_atomic_generation
```

## Invariants

1. Core is complete without optional aspect declarations.
2. Dynamic facets do not alter base layout or nominal parents.
3. `FacetRef<T>` is the only optional typed view.
4. V1 aspects use public contracts or explicit owner capability facades.
5. Variants resolve during build; runtime sees concrete IDs and a fingerprint.
6. SFM owns catalog, directory, compression, signatures, and pack policy; SMF remains an opaque executable code unit.
7. One staged transaction validates every dependency/resource before publishing one generation.
8. Cold catalog entries trigger no pack open, payload read/decompression, mapping, allocation, scan, or config parse.
9. Dynamic facet acquisition and prepared advice execute only through an
   explicitly threaded application execution context; there is no implicit
   process-global/current context.

## Owner boundaries

| Layer/owner | Responsibility | Forbidden coupling |
|---|---|---|
| `compiler/00.common/structural_contracts` | Immutable IDs and `TypePredicateBytecode` shared by frontend/HIR/MIR/loader | No parser, resolver, loader, or runtime implementation logic |
| `compiler/10.frontend` | Proposed facet syntax and selector parsing | No binding coherence or I/O |
| `compiler/20.hir` + type/semantic layers | Contract resolution, descriptor projection, completeness, uniqueness, dependency/access checks | No pack reading or runtime registry mutation |
| `compiler/50.mir`, `85.mdsoc` | Static binding/weaving and dynamic operation schema | No duplicate pointcut evaluator |
| `compiler/80.driver` | Build orchestration and catalog/pack inputs | No new container codec |
| `std.sfm` | Versioned outer manifest, aspect directory, framed payload validation | No SMF symbol/relocation interpretation |
| `compiler/99.loader` | Object-provider adaptation plus reusable staged-loading, publication, and bounded-cache mechanisms | No application policy, source-root, or variant reevaluation |
| `os/smf` | dynSMF policy, status/evidence, activation generation, unload/reload | No second module loader |
| `app/startup` | Owns the process `AspectCatalog`, trust policy, canonical provider-cache instance, stable aspect execution context, and startup-to-operational seal | No raw `rt_*`, pack codec, second module loader/cache, copied lifecycle owner, or process-global context registry |

## Core patterns

- **Generated typed adapter:** `FacetRef<T>` is compiler surface sugar over an
  application-local private `(Base, FacetContract)` adapter containing the
  typed base operand plus an application-owned opaque descriptor-lease handle.
  Contract validation and ordinal lookup remain context-first runtime
  operations; generated code never decodes descriptor layout or erases the
  base to a raw pointer.
- **Feature transform:** type selectors compile once to `TypePredicateBytecode`, then evaluate against closed-world or newly registered descriptors.
- **Provider adapter:** `AspectPackProvider` supplies selected SMF bytes through `ObjectProvider`/`SmfReaderMemory`.
- **Transactional generation:** mapping, relocation, witnesses, advice, and resources stage privately, then publish once.
- **Virtual capsule:** one aspect may span contracts, binding, implementation, tooling, and tests while each leaf consumes only owner facades.

## Implemented owner map

| Owner | Current implementation surface |
|---|---|
| shared predicate contract | `compiler/00.common/predicate.spl`, `structural_contracts/aop.spl` |
| proposed facet syntax/HIR | `compiler/10.frontend/facet_static.spl`, `compiler/20.hir/facet_static.spl` |
| closed-world coherence | `compiler/35.semantics/facet_coherence.spl` |
| typed acquisition | `std.aop.facet` |
| build-time aspect roots | `compiler/99.loader/module_resolver/var_resolution.spl` |
| outer pack codec | `std.sfm.aspect_pack` (`SFM2`; opaque SMF frames) |
| existing-reader adapter | `compiler/99.loader/loader/aspect_pack_provider.spl` |
| catalog and generation adapter | `compiler/99.loader/loader/aspect_catalog.spl`, `aspect_activation.spl` |
| dynamic facet publication | `compiler/99.loader/loader/facet_binding_registry.spl` (validated candidates, exact `activation_key@generation` publication, concrete/open-world lookup, exact unbind; no lifecycle ownership) |
| facet artifact contract | `compiler/00.common/structural_contracts/facet_artifact.spl`; SHB v1.1 optional facet-contract section and ordinary-SMF `.facet_bindings` Note consumed through existing readers |
| dynamic advice publication | `compiler/99.loader/loader/advice_binding_registry.spl` (catalog-prepared slots, canonical preordered chains, exact-generation publish/unbind, disabled-path counters; no pointcut evaluator). Its current lifecycle/callback executor is the audited cohesion violation described below. |
| application runtime owner | `app/startup/aspect_application_runtime.spl` (retained trust/cache/coordinator, exact relative routes, mission seal, opaque per-aspect generation leases, quiesce/drain unload) |

The syntax parser is an explicitly feature-scoped frontend surface; it does not
replace the established advice/CE parsers. The activation adapter composes
`DynSmfSession`, `CandidateMapping`, `GenerationState`, and `LifecycleManager`;
it does not own executable relocation or a second module discovery path.
Production activation stages facet and advice candidates only after the module
loader validates witness ownership. Advice targets must occur in the catalog's
prepared-slot set. Both registry publications and lifecycle promotion are
computed before one coordinator value becomes visible. Advice lookup preserves
existing AOP order (priority, specificity, witness name), never re-evaluates
pointcuts, and exposes the non-zero prepared-slot guard through deterministic
counters and a footprint descriptor. The application runtime removes both
facet and advice visibility before unload drain. Mission policy rejects runtime
advice-patch activation.

`advice_dispatch_slot` is the current loader-validated sequential execution seam for
zero-argument `before`, `after_success`, and `after_error` witnesses. Admission
captures the resolved address and owner; dispatch revalidates both against the
existing `ModuleLoader` before invoking any callback, so an invalid chain fails
before partial execution. Runtime `around` is rejected because no dynamic
exactly-once `proceed` continuation exists. With
`CompileOptions.prepared_dynamic_advice`, the established pointcut/weaving authority now
produces stable execution slots and automatic phase-specific
`simple.prepared_advice_dispatch.v1` MIR intrinsics. They remain non-executable
until the lifecycle-safe backend bridge below is complete.

The shared `PreparedAdviceSlotPlan` contract carries schema ID/version, stable
slot ID, target function identity, and admitted before/after forms.
`MirModule.prepared_advice_slots` preserves this table through normal/bootstrap
lowering, AOP/debug reconstruction, MIR optimizers, and VHDL aggregation;
`serialize_mir_prepared_advice_slots` provides deterministic handoff bytes.
The driver collects a deterministic schema-v1 table. The loader derives an
immutable schema-v1 dispatch projection containing exact publication,
generation, witness-owner, and address identity from its canonical registry.
Projection install is atomic with publication and invalidation precedes drain.
Sequential application-runtime dispatch pins the exact generation; concurrent
pin visibility requires the audited state-gate split below. Check/interpreter
reject the option directly; JIT and every AOT backend reject produced slots
before code generation until they can reach that canonical dispatch owner.

## Ownership boundaries

### Resolver installation dependency

The resolver-installation inversion is closed through
`85.mdsoc/feature/module_loading/app/ModuleResolverDiscoveryPort`.
Its frozen `resolve_inputs(inputs) -> Result<ModuleResolverPort, text>` operation
returns the existing immutable roots/fingerprint contract. The 99-loader aspect
registry adapter implements discovery; production CLI composition injects it
before phase-one collection. Layer 80 imports only the application port and the
shared path policy in layer 00, with no loader implementation dependency.
Compatibility constructors intentionally inject the empty discovery port.

### Prepared dynamic join points

`MirModule` carries deterministic prepared-slot metadata and the explicit
config producer inserts phase-specific prepared-dispatch intrinsics. Catalog
slot strings and the loader projection consume the same finite slot identity;
no runtime pointcut evaluator is introduced.

The explicit application execution context bridge is implemented for the
admitted sequential path. `AspectExecutionContext` is the sole stored owner of the
loader, lifecycle manager, facet/advice registries, and dispatch projection.
The driver validates the exact context argument and rewrites v2 to an ordinary
source-owned dispatch call; no generated backend trampoline or process-global
handle is admitted. Projection publication, invalidation, and exact-generation
pinning remain context-owned loader/application-runtime responsibilities.
Concurrent mutation is not safe until the callback-safe application state gate
below exists. The projection is never an independently mutable registry.

### Facet witness descriptors

Facet binding artifact v3 carries `FacetWitnessDescriptorV1` as inert wire
metadata: exact contract ABI hash, inert descriptor identity/method prefix, and
contract-ordered method names/symbols. The wire encoder rejects any populated
runtime owner or resolved address, so authority cannot be silently erased by
serialization. After ordinary-SMF mapping, the existing `ModuleLoader` resolves
every entry to one exact owner and positive address; the loader registry stores
that resolved state and the application runtime returns an opaque whole-contract
lease handle. A context-first accessor validates the retained generation and
returns only the compile-time ordinal's checked method address. The descriptor
identity is never called or required as an exported factory. Inherited table
flattening and generic descriptor shapes remain fail-closed.

The current intrinsic ABI is intentionally insufficient for that bridge: it
carries only the stable slot and phase, not a canonical lifecycle handle or
generation token. A process-global native projection with its own reference
count would therefore introduce a second lease authority rather than pinning
the loader's `LifecycleManager` generation. Until lowering can acquire the
canonical token through the explicit typed execution context, no
backend-visible table or trampoline is installed and the common backend/driver
E-AF010 rejection is the required behavior. Raw callback-address invocation
alone does not close the unload race.

The reviewed successor ABI is
`simple.prepared_advice_dispatch.v2(context, slot, phase)`. Opt-in targets must
declare one exact typed context parameter; missing, ambiguous, copied, or
wrong-typed contexts are compile errors. A driver MIR pass validates the exact
argument local and rewrites v2 to an ordinary direct call of the
source-owned `prepared_advice_dispatch_context_invoke` entry, so existing call
ABIs—not backend-specific callback code—carry the context. Every residual v1
or v2 intrinsic remains a backend error.

This ABI becomes executable only after a stable application reference capsule
is the sole owner of `LifecycleManager`, `AdviceBindingRegistry`,
`AdviceDispatchProjection`, and the validating `ModuleLoader`; coordinator and
runtime values must reference that capsule rather than copy its mutable state.
The dispatcher applies returned registry/lifecycle state synchronously and may
surface failure only after exact-token cleanup. Initial admission is hosted CPU
AOT entry-closure; interpreter, JIT, SMF-exec, GPU, WASM, VHDL, and unproved
native paths remain E-AF010. Two-context isolation, held-token unload blocking,
entry-closure inclusion, and residual-intrinsic rejection are mandatory gates.

The same stable capsule is the lexical acquisition owner for dynamic facets.
The compiler generates a private typed `(Base, FacetContract)` adapter rather
than relying on the unimplemented native `dyn Trait` vtable path or erasing the
base to `Any`/a raw address. Dynamic refs are affine lexical guards whose lease
is released through that exact capsule on every exit.

## Cache and invalidation

Validated index keys include catalog generation, pack digest, target, variant fingerprint, runtime ABI, core public ABI hash, and core layout ABI hash. Decoded module keys also include module digest. Catalog/digest/generation/semantic changes invalidate positive and bounded negative entries. Eviction respects module-generation pins and resource refcounts. There is no request-time full-tree scan, repeated source read, or subprocess.

## Compatibility

Existing `on pc{...} use ...`, ordinary SMF v0.1, current dynSMF controls/evidence, and current variant precedence remain compatible. New syntax and dynamic patching are feature-gated. `AspectPackProvider` is introduced only after the byte-backed loader seam is proven.
## 2026-08-04 exact-generation prepared-advice dispatch addendum

`AdviceDispatchProjection` remains the immutable loader-derived dispatch
interface; it is not a second publication or lifecycle registry. Loader-backed
activation derives the complete projection from the newly computed canonical
`AdviceBindingRegistry` before `AspectActivationCoordinator` atomically exposes
the registry, projection, and promoted `LifecycleManager` generation.

Each phase dispatch acquires one opaque `GenerationToken` for every projected
entry's exact `(activation_key, generation)`, validates that the entry still
matches both the canonical publication and the `ModuleLoader` owner/address,
invokes the already ordered phase chain, and releases those exact tokens in
reverse order on success and every validation/acquisition/callback failure.
Unload removes facet visibility, advice visibility, and the exact projection
rows before quiescing and testing drain. No process-global dispatch table,
runtime pointcut scan, raw runtime boundary, or backend-specific lifecycle path
is introduced.

The former registry-plus-loader executor is not part of the public surface:
native execution is reachable only through the projection-plus-lifecycle seam.
Canonical registry lookup remains separately available for inspection.

## 2026-08-04 callback-safe advice concurrency audit

### Current state

The exact-generation algorithm is sequentially correct but is not currently a
concurrent ownership boundary. `advice_dispatch_projection_with_invoker` in
`compiler/99.loader/loader/advice_binding_registry.spl` receives value snapshots
of `AdviceBindingRegistry` and `LifecycleManager`, acquires tokens in the local
lifecycle value, invokes callbacks, and returns updated values. Only afterward
does `AspectExecutionContext.invoke_prepared_advice` assign those values back to
the application context. No mutex covers that copy-in/copy-out interval.

Consequently, concurrent dispatches can start from the same token counter and
lose pin/counter updates, while `unload_published_aspect` can invalidate,
quiesce, observe the canonical pin count as zero, and reclaim loader resources
while a callback is running with pins held only in a local lifecycle copy. The
existing tests prove ordering, validation, cleanup, and sequential unload retry;
they do not prove concurrent dispatch/unload safety. `LifecycleManager` remains
the correct sole generation-lease registry, but its immutable-copy API requires
one serialized application owner for every mutation.

The context methods `advice_dispatch_slot(loader, ...)` and
`unload_published_aspect(..., loader)` also overwrite `self.loader` from a
caller-supplied `ModuleLoader` value. That compatibility shape permits a stale
loader copy to replace the supposed canonical owner and must not be used by the
concurrent path; context-owned operations must use only `self.loader`.

The current module also violates its stated cohesion boundary: the loader
registry owns publication data but imports `LifecycleManager`, `ModuleLoader`,
and the native callback primitive and performs callback execution. Registry
publication, generation leasing, physical resource ownership, and application
synchronization are distinct concerns.

### Required owner split

| Raw layer | Common/owned node | Public to parent | Public to next-layer sibling |
|---|---|---|---|
| `compiler/99.loader` | advice publication registry | immutable ordered records, publish/unbind/lookup | projection derivation only |
| `compiler/99.loader` | immutable dispatch projection | exact owner/symbol/address/generation rows | validated invocation plan to `app/startup` |
| `os/smf` | generation lifecycle | acquire/release exact opaque tokens; quiesce/drain | no registry or callback execution |
| `compiler/99.loader` | module/resource lifecycle | validate loaded owner/address; unload mapped owners | no generation-pin authority |
| `app/startup` | advice dispatch coordination | context-first dispatch result | sole serialized mutation of registry/lifecycle/projection |
| `app/startup` | retirement coordination | visibility invalidation then quiesce/drain/unload | sole ordering bridge between generation and physical owners |

Tree-private implementation should split as follows without new language
visibility grammar:

1. Keep candidate staging, deterministic ordering, publication, lookup, and
   unbind in `advice_binding_registry.spl`. Retain publication/lookup counters
   there, but move dispatch attempt/invocation/failure counters into the
   application dispatch coordinator that serializes their mutation.
2. Move projection derivation/invalidation and loader-owner validation to a
   loader-private projection module. It returns immutable rows and never owns
   tokens or invokes callbacks.
3. Add an application-private dispatch coordinator beside
   `AspectExecutionContext`. Under one application state mutex it revalidates
   the current projection/publication, acquires exact lifecycle tokens, commits
   the updated canonical lifecycle and attempt counters, and returns a
   tree-private dispatch ticket.
   The concurrent entrypoint accepts no caller-supplied `ModuleLoader`; it uses
   the context's retained loader exclusively.
4. Release the state mutex before invoking any callback. This is mandatory for
   callback re-entry and for callbacks that request unload; no application or
   lifecycle lock may be held across foreign/generated code.
5. In a guaranteed finish path, reacquire the same state mutex, release the
   ticket's exact tokens in reverse order, commit counters/lifecycle, then
   expose success or failure. Portable unwind/cancellation remains blocked until
   the language can guarantee this finish path.
6. Serialize activation publication and unload invalidation/quiesce through the
   same application state mutex. Unload commits invisibility and quiescing
   before checking pins, returns `quiescing` while tickets exist, and claims one
   retirement completion before performing physical `ModuleLoader` cleanup so
   concurrent retries cannot unload twice.

The lazy-activation single-flight gate is not this state mutex and must not be
reused as one: it coordinates one I/O/activation request and intentionally
releases its lock around callbacks. The advice state mutex protects canonical
publication/lifecycle mutation; the two gates have different keys and owners.

This split retains MDSOC direction: loader owns inert validated projection,
`os/smf` owns leases, and the application capsule composes them. No process-global
table, second reference count, copied runtime snapshot, or backend-owned pin is
admitted.
