<!-- codex-design -->
# System Test Plan: Aspect Facets and Demand-Loaded SFM Packs

## Frozen primary flow

1. `step("Inspect the application Aspect Catalog")`
2. `step("Acquire the optional facet")`
3. `step("Load only the selected SMF module closure")`
4. `step("Publish the facet generation atomically")`
5. `step("Reject an invalid aspect pack")`

Reusable hidden setup/check helpers are `build_aspect_pack_fixture`, `verify_cold_aspect_counters`, and `verify_atomic_activation`. Unimplemented helpers must call `assert(false)` or `fail(...)`.

## Scenario matrix

| Spec | Requirements | Primary evidence |
|---|---|---|
| `test/03_system/feature/language/aop/aspect_facet_static_binding_spec.spl` | REQ-AF-001..003, 009..010 | Concrete/interface selection, stable layout, explicit `FacetRef<T>`, public capability boundary, existing AOP preservation |
| `test/03_system/compiler/module_resolver/relative_aspect_roots_spec.spl` | REQ-AF-004, 007 | Manifest-relative resolution independent of CWD; collision/path/symlink escape; build-time variants only |
| `test/03_system/stdlib/dynload/aspect_pack_selective_loading_spec.spl` | REQ-AF-005, 007; NFR-AF-004, 008 | Real SFM directory + opaque SMF chunks; only selected closure decoded; corrupt/bounds/hash/ABI/config failures |
| `test/03_system/app/simple/aspect_catalog_activation_spec.spl` | REQ-AF-003, 006..008; NFR-AF-001, 002, partial 006 | Catalog routing, base/aspect load order, cold counters, cache invalidation, shared concurrent transaction, atomic generation; no backend footprint or retained-performance claim |
| `test/01_unit/scripts/aspect_facet_nfr_evidence_contract_spec.spl` | NFR-AF-005 | Exact admitted compiler/probe/fixture/protocol provenance, deterministic native advice outcome, receiver-aware facet-call fail-closed gate, cold-isolation counters, distinct opened files, latency percentiles, cache/advice accounting, and no invented thresholds |

## Retained NFR evidence

`scripts/check/build-aspect-facet-nfr-probe.shs` is the canonical admitted build
and provenance step; `scripts/check/check-aspect-facet-nfr-evidence.shs` is the
canonical collector. The collector accepts only an exact admitted compiler hash
plus its provenance-bound native probe and fixture,
requires at least 20 samples, and writes
`build/test-artifacts/aspect-facet-nfr/baseline.sdn`. The first admitted run is
recorded as `collected-not-thresholded`; host thresholds are selected only from
that retained baseline and then checked in with the binary and fixture hashes.

## Manual design

Each executable spec mirrors to `doc/06_spec` after stripping `test/`. Fixture creation is `@inline`; follow-up failure/matrix scenarios use `@prev` where supported. The five frozen steps form the visible operator flow. Detailed corrupt-input and concurrency matrices are folded. Assertions use built-in matchers only and include absolute counters/oracles so empty or same-path equality cannot pass.

## Verification policy

- Run each changed spec once per unchanged implementation in interpreter mode; add native evidence only where ABI/loading behavior requires it.
- Generate each mirror once and require `0 stubs`.
- Run `sspec-maintain scan` once per final spec and review all seven scores.
- Keep manifest counts dynamic; never pin the current dynSMF entry count or absolute evidence indexes.
- Fail closed on an unavailable required capability; do not use `skip()` or placeholder passes.
