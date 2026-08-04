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
| D3 backend trampoline | Backend intrinsic lowering and process-visible immutable projection bridge, only if end-to-end executable | `simple.prepared_advice_dispatch.v1`; unsupported targets remain E-AF010 |

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

## Cooperative review

- Completed read-only sidecars: `design_audit`, `implementation_gap`, `spec_and_requirements`.
- Implementation sidecars: bounded lanes P1/P2/P6 may proceed in parallel after the merge owner confirms exact existing owners and non-overlap.
- Merge owner: root Codex.
- Generated-manual review owner: root Codex.
- Final normal/highest-capability reviewer: root Codex.
- Lower-model/manual done marks are advisory until final review.

## Merge order

P1 and P2 first; P4 and P3 second; P6 may merge independently; P5 integrates last. Run only focused gates during lane work. Broad verification occurs once after integration.
