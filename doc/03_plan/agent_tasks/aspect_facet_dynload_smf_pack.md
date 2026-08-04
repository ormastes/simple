<!-- codex-design -->
# Agent Tasks: Aspect Facets and Demand-Loaded SFM Packs

## Shared contract frozen before fan-out

- Interfaces/types: `FacetRef<T>`, `FacetBindingPlan`, `TypePredicateBytecode`, `AspectCatalog`, `AspectPackDirectory`, `AspectPackProvider`.
- Manual steps: the five exact phrases in `doc/03_plan/sys_test/aspect_facet_dynload_smf_pack.md`.
- Setup/checkers: `build_aspect_pack_fixture`, `verify_cold_aspect_counters`, `verify_atomic_activation`.
- Temporary implementation: explicit `assert(false)` or `fail(...)`; never a passing stub.

## Parallel lanes

| Lane | Owned scope | Dependencies | Handoff |
|---|---|---|---|
| P1 type predicates | shared contract, compile-time descriptor projection, parser/evaluator tests | none | reviewed `TypePredicateBytecode` contract |
| P2 SFM pack codec | `std.sfm` aspect directory/framed opaque payload codec and unit tests | frozen directory schema | bounded validated byte API |
| P3 loader adapter | `AspectPackProvider` -> `ObjectProvider` and staged byte-backed load | P2 byte API | focused loader/provider tests |
| P4 facet semantics | AST/HIR/coherence/static `FacetRef<T>` | P1 | static binding system spec |
| P5 catalog/lifecycle | `AspectCatalog`, dynSMF adapter, atomic publication/cache policy | P2/P3/P4 metadata | activation system spec and retained counters |
| P6 resolver roots | manifest-relative aspect roots reusing variant helpers | frozen resolver contract | resolver system spec |

## Continuation lanes (2026-08-04)

| Lane | Owned scope | Frozen handoff |
|---|---|---|
| C1 artifact/codegen | common facet artifact metadata, SHB compatibility, ordinary-SMF note emission, witness lowering | deterministic codecs and public probe/fixture APIs |
| C2 driver registry | one canonical `ModuleResolverPort`, automatic aspect-registry install, fingerprinted driver identity, hidden-import rejection | focused executable spec and manual |
| C3 advice runtime | loader-owned advice generation registry, prepared slots, publish/unbind ordering, mission denial, counters | app-facade counters and explicit contract-only disabled footprint |
| C4 NFR evidence | admitted-binary collector, native probe, representative fixture, retained baseline schema | `aspect_facet_perf_summary` and provenance-bound SDN |

## Bounded backend review lanes (2026-08-04)

| Lane | Result | Residual |
|---|---|---|
| B1 facet witness ABI | Canonical symbol naming plus emitted-symbol proof; declaration-only plans fail closed | Executable facet bodies, ABI adapter/export, and frontend call lowering |
| B2 advice dispatch | Exact-generation owner/address validation and zero-argument before/after dispatch; dynamic `around` denied | Prepared MIR slot producer and automatic business-path caller |
| B3 architecture | Verified resolver and prepared-slot owner boundaries without unsafe partial extraction | `85.mdsoc` resolver injection and `50.mir` → optimizer → backend → driver slot pipeline |

## Production bridge continuation lanes (2026-08-04)

| Lane | Owned scope | Frozen handoff |
|---|---|---|
| D1 facet descriptor | Common descriptor, ordered method entries, ordinary-SMF artifact, loader resolution | `FacetWitnessDescriptorV1`, `FacetWitnessMethodEntry`, `facet_witness_descriptor_from_contract`, `facet_resolve_witness_descriptor` |
| D2 advice lifecycle | Canonical-registry projection publication, exact `GenerationToken` pin/release, invalidate-before-drain | Existing `AdviceDispatchProjection`; no second registry or raw runtime shortcut |
| D3 backend trampoline | **Superseded/cancelled by D4:** do not install a process-visible bridge; keep residual v1 fail-closed | v1 remains E-AF010; D4 owns the explicit-context v2 successor |
| D4 execution context | Refactor one stable application reference capsule to own loader, lifecycle, registries, and projection; validate/rewrite explicit-context v2 to an ordinary call | `AspectExecutionContext`, `simple.prepared_advice_dispatch.v2(context, slot, phase)`, `prepared_advice_dispatch_context_invoke` |
| D5 typed facet adapter | Generate private `(Base, FacetContract)` adapter, acquire the complete descriptor once, select by ordinal, and release the affine lease on all exits | Existing `FacetRef<T>`, `FacetWitnessDescriptorV1`, `lower_resolved_facet_witness_method_call`; no dyn-trait or erased-base ABI |

Current implementation status:

- D4 implemented pending executable verification: the stable `AspectExecutionContext` class, compatibility type
  alias, context-owned dispatcher, two-context isolation coverage, exact-token
  cleanup coverage, typed v2 producer, independent driver validation, exact
  source-owned fail-stop wrapper proof, ordinary unit-call rewrite, per-slot
  coverage proof, and residual v1/v2 rejection exist. Failure cleanup completes
  before canonical panic; arbitrary business return values remain untouched.
- D5 partial: typed-base adapter planning, descriptor version/hash/count/order/
  name/owner/address validation, base-first indirect-call selection, erased-base
  rejection, genuine parser/AST/HIR acquisition and member provenance, real
  symbol-based escape checks, and context-first whole-descriptor acquisition/
  release APIs exist. Exact nominal context/contract proof, canonical member
  ordinal/signature resolution, runtime lease-to-adapter lowering, checked
  method-address access, and lambda/async capture rejection now exist.
  Wrapper-aware adapter propagation and reverse-order release now cover every
  modeled lexical exit. Exact-route lazy activation and canonical
  `FacetAcquireError` are wired; unsupported leased `throw`/suspension and
  identifiable extern-unwind paths fail closed. Production I/O-port binding,
  true multithreaded single-flight completion, indirect/imported unwind
  metadata, and language-sealed lease opacity remain open.

These lanes retain the five system-manual phrases already frozen in the system
test plan. Focused setup/checker helpers are
`build_facet_witness_descriptor_fixture`,
`verify_exact_generation_advice_dispatch`, and
`verify_prepared_advice_backend_bridge`. Any temporary helper fails with
`assert(false)` or `fail(...)`; no placeholder factory or silent intrinsic
lowering is admissible.

The merge owner remains root Codex. C1/C2/C3 run in parallel; C4 integrates
their public handoffs. Root performs the final normal/highest-capability review
and the one admissible focused verification sweep.

D4 must land before D5 or executable v2 admission because both require the
same canonical application-owned state. D4 acceptance includes two-context
isolation, held-token unload blocking, exact cleanup before failure, entry-
closure inclusion, and residual v1/v2 rejection. D5 acceptance includes exact
descriptor count/order/name validation, a typed base operand at ABI argument
zero, no dynamic-ref escape, and one balanced acquire/release per retained ref.

## D4/D5 implementation order

1. Introduce the stable `AspectExecutionContext` reference capsule at the
   application composition owner and move loader/lifecycle/registry/projection
   ownership into it. Preserve compatibility facades as references, never
   value snapshots.
2. Refactor activation, dispatch, facet lease acquisition/release, and unload
   to mutate that one capsule. Prove two contexts are isolated and an in-flight
   token prevents unload drain.
3. Extend prepared-target validation to require exactly one typed context Arg;
   emit v2 with `Copy` of that Arg plus constant slot/phase. Missing or wrong
   context fails before MIR publication.
4. **Implemented, verification pending:** fail-stop dispatcher semantics and
   validated v2 ordinary-call rewrite;
   keep v1/v2 residual rejection in every backend and admit hosted CPU AOT
   entry-closure only after link/ABI evidence.
5. **Partially implemented:** wire source/HIR facet acquisition and generate one private typed adapter per
   `(Base, FacetContract)`, construct it
   from one whole-descriptor acquisition, and lower member selection by exact
   contract ordinal through the existing base-first indirect-call helper.
6. Add affine escape analysis and compiler-inserted release on normal, error,
   and early exits. Reject copy, return, global/store, async, and thread escape.
7. Update focused SSpecs/manuals and NFR probe; then run one bounded verify
   cycle. Do not use source-text or boolean-wrapper assertions.

## Cooperative review

- Completed read-only sidecars: `design_audit`, `implementation_gap`, `spec_and_requirements`.
- Implementation sidecars: bounded lanes P1/P2/P6 may proceed in parallel after the merge owner confirms exact existing owners and non-overlap.
- Merge owner: root Codex.
- Generated-manual review owner: root Codex.
- Final normal/highest-capability reviewer: root Codex.
- Lower-model/manual done marks are advisory until final review.

## Merge order

P1 and P2 first; P4 and P3 second; P6 may merge independently; P5 integrates last. Run only focused gates during lane work. Broad verification occurs once after integration.
