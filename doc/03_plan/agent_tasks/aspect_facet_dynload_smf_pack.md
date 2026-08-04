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

## Cooperative review

- Completed read-only sidecars: `design_audit`, `implementation_gap`, `spec_and_requirements`.
- Implementation sidecars: bounded lanes P1/P2/P6 may proceed in parallel after the merge owner confirms exact existing owners and non-overlap.
- Merge owner: root Codex.
- Generated-manual review owner: root Codex.
- Final normal/highest-capability reviewer: root Codex.
- Lower-model/manual done marks are advisory until final review.

## Merge order

P1 and P2 first; P4 and P3 second; P6 may merge independently; P5 integrates last. Run only focused gates during lane work. Broad verification occurs once after integration.

