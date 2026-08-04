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
- AC-10: The production compiler automatically installs the resolver-owned
  aspect registry for real compile inputs, carries its fingerprint through
  resolution/cache identity, and rejects business imports from hidden roots.
- AC-11: Facet contracts are emitted into canonical SHB metadata and validated
  MIR facet plans into ordinary-SMF metadata, consumed by production
  witness-call lowering and published through the existing loader; dynamic
  advice uses prepared slots with exact-generation bind/unbind and the existing
  AOP exactly-once ordering.
- AC-12: Retained NFR evidence binds an admitted pure-Simple binary and fixture
  hashes to cold startup wall/RSS/page-fault/file-I/O counters, first-use
  p50/p95/p99, repeated lookup cost, and exact cache counters; unavailable
  executable evidence remains a release blocker rather than a synthetic PASS.

## Scope Exclusions
Release/version bump/tagging and pushing `main` are excluded. The dedicated WIP
feature bookmark may be synchronized for collaboration while the verification
report remains explicit `STATUS: FAIL`. Arbitrary private-layout/mutating
facets are deferred from V1.

## Cooperative Review
Completed read-only sidecars: `design_audit`, `implementation_gap`,
`spec_and_requirements`. Completed implementation lanes include
`impl_type_predicate`, `impl_sfm_pack`, `impl_aspect_roots`, lifecycle/cache,
application activation, MIR metadata, and loader facet registry. Completed
continuation lanes are `driver_registry_install`, `artifact_witness_lowering`,
`dynamic_advice_registry`, and the NFR probe/collector. Frozen shared runtime primitive names are
`facet_lookup`, `facet_bind_type`, `facet_unbind_generation`,
`advice_bind_slot`, `advice_unbind_generation`, and
`aspect_publish_generation`. Frozen manual steps/helpers remain AC-7. Merge
NFR evidence interfaces are
`build_aspect_perf_fixture`, `measure_cold_aspect_startup`,
`measure_first_facet_use`, `measure_repeated_facet_lookup`, and
`aspect_facet_perf_summary`, driven by
`scripts/check/check-aspect-facet-nfr-evidence.shs`. Merge
owner, generated-manual reviewer, and final normal/highest-capability reviewer:
root Codex. Temporary helpers fail with `assert(false)` or `fail(...)`.

## Phase
verification-failed

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
- sync: feature bookmark rebased and pushed at `3addf7aaad75`, then rebased
  cleanly again onto current `main@origin` before the continuation lanes.
- implementation: continuation opened three parallel lanes for canonical
  driver registry installation, SHB/SMF witness lowering, and dynamic advice
  slots; NFR-AF-005 retained measurement evidence remains root-owned.
- implementation: automatic registry installation, SHB facet contracts,
  ordinary-SMF binding metadata, exact-generation advice publication, and the
  provenance-bound native NFR fixture/probe/collector were integrated. Final
  review fixed importer/cache authorization leaks, UTF-8/count codec defects,
  malformed artifact fail-open paths, and native pointer-order sorting.
- verification: the one final continuation sweep passed shell syntax,
  placeholder/conflict/trailing-whitespace scans, both direct-env/runtime
  guards, and `doc/06_spec` layout count `0`. AC-11 remains incomplete because
  production facet witness generation/call consumption and advice invocation
  are absent; AC-12 lacks an admitted runtime baseline. Authoritative status is
  `STATUS: FAIL`.
- implementation: a second bounded parallel review centralized
  `facet_witness_symbol`, made ordinary-SMF facet metadata fail closed without
  an actually exported witness, added loader-owned zero-argument
  `advice_dispatch_slot` for before/after phases, and rejected dynamic `around`
  without an exactly-once proceed continuation.
- architecture: the same review proved that automatic prepared-slot production
  still needs `50.mir` metadata, optimizer preservation, `70.backend` lowering,
  and `80.driver` table emission. The resolver direction remains open until
  discovery is injected through the existing `85.mdsoc` module-loading port.
- verification: AC-11 remains incomplete because facet declarations have no
  executable witness bodies/call lowering and no generated business-path caller
  invokes `advice_dispatch_slot`. Runtime, docgen, NFR, and coverage blockers
  remain unchanged; authoritative status remains `STATUS: FAIL`.
- implementation: the August 4 continuation closed the resolver layering
  inversion, added receiver-aware facet method MIR lowering and deterministic
  multi-symbol SMF validation, and produced overload-safe prepared-advice MIR
  phase calls plus loader-derived dispatch projections. Backend admission now
  fails closed across check/interpreter/JIT/AOT and at the common backend edge.
- verification: production remains deliberately blocked: the canonical facet
  factory/descriptor ABI and generated caller are undefined, prepared-advice
  projection publication/generation pinning/backend trampoline are absent, and
  admitted runtime/NFR evidence could not run under the bounded bootstrap cap.
  The authoritative report therefore remains `STATUS: FAIL`.
- implementation: the production-bridge continuation froze
  `FacetWitnessDescriptorV1`, ordered `FacetWitnessMethodEntry` resolution, the
  existing immutable `AdviceDispatchProjection`, and exact `GenerationToken`
  dispatch pinning before parallel D1/D2/D3 work. The backend intrinsic may
  become executable only through a real process-visible derived projection;
  unsupported paths keep E-AF010.
- architecture: runtime_need for D3 is an atomic process-visible projection
  snapshot plus indirect callback invocation. Existing pure-Simple loader and
  lifecycle facades were checked first. chosen_path remains
  `reuse-facade`/`add-smallest-owner-facade` unless D3 proves that a smallest
  runtime-owned atomic primitive is unavoidable. rejected_shortcuts are a
  second authoritative registry, mutable module-global Simple state, fixture
  bypasses, and silently dropping the MIR intrinsic.
- architecture: D3 feasibility review checked the loader's
  `native_call_function_0` callback primitive, the canonical
  `GenerationToken`/`LifecycleManager` dispatch path, the driver artifact gate,
  and Cranelift/LLVM/native intrinsic lowering. The emitted
  `simple.prepared_advice_dispatch.v1` ABI carries only `(slot, phase)` and
  therefore cannot acquire or prove the canonical loader generation. A native
  process-global snapshot would become a second lease authority and cannot be
  made end-to-end lifecycle-safe by a facade alone. chosen_path is consequently
  `fail-closed-pending-token-bearing-ABI`; rejected_shortcuts additionally
  include an independently reference-counted C table and callback invocation
  without a canonical loader pin. No runtime owner edit was made.
## 2026-08-04 — exact-generation prepared-advice dispatch lifecycle

- Kept `AdviceDispatchProjection` as the frozen loader-derived interface; no
  second registry, process-global projection, raw runtime boundary, or backend
  lowering was added.
- Added typed acquire/validate/invoke/release dispatch over canonical
  `LifecycleManager` tokens, including exact cleanup receipts for success,
  partial acquisition failure, loader validation failure, and callback failure.
- Loader-backed activation now derives projection with canonical publication;
  unload atomically removes facet/advice/projection visibility while quiescing,
  before drain evaluation.
- Added behavioral unit evidence for stale/forged generations, cleanup on
  validation/callback failures, exact chain order, and invalidation/quiesce
  ordering. Static direct-env runtime guard: PASS. Compiler/bootstrap not run by
  explicit lane constraint.
- Final review removed the legacy exported registry-plus-loader native executor
  and its outcome type. Public execution now has no bypass around the required
  projection and canonical lifecycle arguments; registry lookup remains public.
