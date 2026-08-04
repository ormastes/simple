# Feature: Aspect Facets and Demand-Loaded SFM Packs

## Raw Request
`$sp_dev sync gh and check aspect_facet_dynload_smf_pack_design ...md update if it not match current simple design and principle. and imple with pherallel agents.`

## Task Type
feature

## Refined Goal
Align the referenced optional-facet design with current Simple architecture, then implement typed structural selection, SFM-pack selective loading, deterministic resolution, and atomic dynSMF lifecycle integration through existing owners.

## Acceptance Criteria
- AC-1: The design and all downstream artifacts use SFM for the outer aspect pack and opaque ordinary SMF module payloads.
- AC-2: Final feature/NFR requirements prove core independence, stable base layout, explicit `FacetRef<T>`, deterministic `TypePredicateBytecode`, fail-closed validation, selective loading, and exact overhead claims.
- AC-3: MDSOC owner boundaries extend current AOP, resolver, SFM, object-provider/loader, dynSMF, cache, and facade owners without a parallel subsystem.
- AC-4: Executable SSpec/manual pairs cover static binding, relative aspect roots, selective SFM payload loading, catalog routing, both registration orders, cold counters, cache invalidation, failure paths, and atomic activation.
- AC-5: Implementation is pure-Simple-first, contains no passing stubs, and has focused unit/integration coverage with at least 80% branch coverage for new logic.
- AC-6: Frozen interfaces are `FacetRef<T>`, `FacetBindingPlan`, `TypePredicateBytecode`, `AspectCatalog`, `AspectPackDirectory`, and `AspectPackProvider`.
- AC-7: Frozen visible steps are `Inspect the application Aspect Catalog`, `Acquire the optional facet`, `Load only the selected SMF module closure`, `Publish the facet generation atomically`, and `Reject an invalid aspect pack`; helpers are `build_aspect_pack_fixture`, `verify_cold_aspect_counters`, and `verify_atomic_activation`.
- AC-8: Verification runs focused checks once, both direct-env/runtime guards, stub/placeholder/requirement tracing, generated-layout count `0`, and final high-capability review.
- AC-9: Only isolated lane files are integrated; unrelated dirty work is untouched.

## Scope Exclusions
Release/version bump/tagging is excluded. Arbitrary private-layout/mutating facets are deferred from V1. Push waits for verified completion.

## Cooperative Review
Completed read-only sidecars: `design_audit`, `implementation_gap`, `spec_and_requirements`. Parallel implementation lanes: `impl_type_predicate`, `impl_sfm_pack`, `impl_aspect_roots`. Merge owner, generated-manual reviewer, and final normal/highest-capability reviewer: root Codex. Temporary helpers fail with `assert(false)` or `fail(...)`.

## Phase
verification_failed

## Log
- dev: acceptance criteria and frozen vocabulary recorded.
- research: local/domain research and selected requirements written.
- design: architecture, revised detail design, test plan, and agent task split written.
- implementation: first parallel wave started.
- implementation: parallel predicate, root, SFM2 codec/provider, static facet,
  catalog, activation, and executable-spec lanes integrated in the isolated
  workspace; root review corrected canonical name matching and owner docs.
- verification: self-hosted feature/docgen attempts reached exit 139 or the
  deployed runtime ABI guard; final static/audit review completed without
  retrying failed criteria.
- verification: facade/layout/spec-shape audits passed; compiler/lib/MCP checks
  exited 139, docgen exited 139, `sspec-maintain` was unavailable, and runtime
  lifecycle/NFR completion remains open. See
  `doc/09_report/verify_aspect_facet_dynload_smf_pack.md` (`STATUS: FAIL`).
- verification: one bounded fresh bootstrap reached Stage 2 discovery/codegen;
  three fix cycles removed a reserved field name and two predicate-parser
  lowering/link defects. The final attempt stopped at the iteration cap, so no
  fourth bootstrap was run and `STATUS: FAIL` remains authoritative.
