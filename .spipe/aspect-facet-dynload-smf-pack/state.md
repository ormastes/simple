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
- verification (historical; superseded by the D1/D2 descriptor/projection work
  and the later D4/D5 review): production remained deliberately blocked: the canonical facet
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

## 2026-08-04 — execution-context prerequisite review

- sync: rebased onto `main@origin` `9c598987bb78` and pushed the isolated WIP
  bookmark at `231cab73e41a`; the worktree was clean after push.
- recovery: the earlier Linux `is_alnum` boundary is superseded in current
  source, and main now includes packed/raw bootstrap return-local repairs.
  Separate ARM64 recovery reached a newer truncated-104-byte LLVM admission
  blocker, but this workspace has no current-source admitted Linux Stage 2/3.
  The safe fresh-session resume command is
  `SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh --backend=llvm --mode=dynload --jobs=2 --no-mcp --progress=build/bootstrap/recovery-20260804.log`.
  No capped compiler/bootstrap command was rerun here.
- architecture: prepared advice and dynamic facet calls share one missing
  prerequisite: a stable application reference capsule that solely owns the
  validating `ModuleLoader`, `LifecycleManager`, facet/advice registries, and
  `AdviceDispatchProjection`. Runtime/coordinator values must reference it,
  never copy the mutable owner state.
- frozen successor interface: `AspectExecutionContext`,
  `simple.prepared_advice_dispatch.v2(context, slot, phase)`, and
  `prepared_advice_dispatch_context_invoke`. The driver validates the exact
  typed context Arg and rewrites v2 to an ordinary direct call; residual v1/v2
  stays E-AF010. Initial admission is hosted CPU AOT entry-closure only.
- facet contract: dynamic `FacetRef<T>` is compiler sugar over a private typed
  `(Base, FacetContract)` adapter containing the concrete base and complete
  resolved descriptor. It selects by canonical method ordinal, emits the
  existing base-first `CallIndirect`, and is an affine lexical guard released
  through the same context on every exit.
- rejected_shortcuts: process-global/current context cells, numeric handle
  registries, copied lifecycle/coordinator state, backend-private callbacks,
  current `dyn Trait` (no production vtable ABI), and `Any`/raw-pointer base
  erasure. `dynamic_facet_ref` remains compatibility-only, not production
  dynamic acquisition evidence.
- cooperative review: `activation_runtime` completed backend/context ABI
  feasibility; `facet_plan_codegen` completed user syntax and typed-adapter
  review; `aspect_registry_driver` completed current-main recovery/provenance
  audit. Root Codex accepted and reconciled the findings.
- doc/wiki refactor: architecture, detail design, agent plan, state, and verify
  report were refreshed. No matching `doc/07_guide` or overlay wiki entry
  exists and no workflow/evidence-wrapper command changed, so guide/skill/wiki
  updates are `N/A` for this architecture-only continuation.
- phase remains `verification-failed`: D4 canonical state ownership and D5
  generated adapter/affine lowering are designed but not implemented; AC-11,
  AC-12, runtime, docgen, maintenance, coverage, and NFR evidence remain open.

## 2026-08-04 — D4/D5 implementation checkpoint

- parallel implementation: `activation_runtime` added the stable
  `AspectExecutionContext` class, current-syntax compatibility type alias,
  context-owned `ModuleLoader`, source dispatcher, two-context isolation, and
  exact-token cleanup coverage. No process-global context or second lifecycle
  registry was introduced.
- parallel implementation: `aspect_registry_driver` added exact typed-context
  v2 production, independent context/slot/phase validation, hosted CPU AOT
  entry-closure gating, and residual v1/v2 rejection. It correctly leaves the
  bridge E-AF010: the dispatcher returns `Result<[i64], text>` and injected
  arbitrary-return targets lack a safe MIR failure-propagation owner.
- parallel implementation: `facet_plan_codegen` added the typed-base adapter
  plan, complete resolved-descriptor validation, base-first indirect-call
  selection, erased-base rejection, and affine escape diagnostics. Source/HIR
  acquisition, application-context descriptor transfer, semantic escape wiring,
  and balanced release insertion remain open.
- root review removed a stale import, replaced deprecated `alias` spelling with
  current `type` syntax, and removed a boolean-wrapper assertion. Compiler
  execution was not repeated after sidecar attempts: one source check passed,
  one focused spec reached 4/5 before an import-only fix, its bounded rerun was
  killed during startup, and the deployed runtime ABI probe failed.
- phase remains `verification-failed`; the new work is a safe, fail-closed
  implementation foundation rather than executable D4/D5 completion.

## 2026-08-04 — executable D4 and source/HIR D5 continuation

- sync: fetched GitHub and confirmed the feature bookmark was already rebased
  on current `main@origin` before edits.
- D4 runtime: added the source-owned unit fail-stop wrapper. It synchronously
  runs the Result dispatcher and stores released-token state before canonical
  panic, preserving arbitrary business return values and preventing continuation
  after advice infrastructure failure.
- D4 compiler: exact dispatcher module/name/signature and entry-closure proof,
  v2-to-ordinary-Call rewriting, slot/phase rewritten-call coverage, artifact
  admission, and residual v1/v2 rejection now exist for hosted CPU AOT
  entry-closure only. D4 is implemented but not executable-verified.
- D5 runtime: added validated context-first whole-descriptor acquisition and
  exact release; no base/view crosses this boundary. Validation failures and
  corrupted aggregate identity release the canonical lease before error.
- D5 compiler: added genuine parser/flat-AST/rich-AST/HIR nodes for
  `context.try_facet<T>(base)`, `facet<T>`, and `require_facet<T>`, HIR member
  provenance, symbol-based copy/return/store/call/spawn checks, and downstream
  traversal preservation. This is not source projection or text scanning.
- D5 remains fail-closed at MIR: exact context-type proof, runtime descriptor
  extraction into the typed adapter, method ordinal/signature resolution,
  complete lambda-capture rejection, and balanced releases on every exit are
  still required.
- no compiler/bootstrap/test command was run in this continuation. Root static
  integration review remains the only admissible verification pass; authoritative
  status remains `verification-failed` / `STATUS: FAIL`.

## 2026-08-04 — D5 typed-adapter continuation

- Exact nominal context and facet-contract identity now use canonical HIR
  symbols; missing members and lambda/async captures fail without text scans.
- MIR retains the concrete typed base separately from the application-owned
  descriptor lease, resolves canonical member metadata, and emits base-first
  indirect dispatch through the context-first checked method accessor.
- CFG-wide reverse-order release and complete `try_facet`/`facet` wrapper
  lowering remain open. No compiler/bootstrap command was run; authoritative
  status remains `verification-failed` / `STATUS: FAIL`.

## 2026-08-04 — D5 wrapper and modeled-exit cleanup continuation

- HIR and MIR now preserve the distinct `Option<T>`,
  `Result<Option<T>, text>`, and `Result<T, text>` acquisition shapes and
  propagate adapter provenance only through successful unwrap/`?` paths.
- Whole-contract validation and ordinal lookup are context-first; generated
  code retains an opaque lease handle and never decodes descriptor fields.
- Compiler-owned lexical cleanup releases guarded leases in reverse order on
  fallthrough, explicit/implicit return, `?` propagation, loop transfer, and
  explicit/generated panic paths.
- Lazy pack I/O, typed acquisition errors, and fail-closed nonlocal-exit guards
  were completed in the following continuation. No compiler or
  bootstrap command was run; status remains `verification-failed` /
  `STATUS: FAIL`.

## 2026-08-04 — D5 exact-route lazy activation continuation

- Added an injected application-owned `AspectPackIoPort`; requests contain
  only the catalog-derived relative path and complete provider identity.
- `facet`/`require_facet` now reserve before I/O, reuse the canonical
  loader/cache/coordinator transaction, and return canonical
  `std.aop.FacetAcquireError`; `try_facet` remains strictly no-I/O.
- Leased scopes fail E-AF007 for `throw`, `await`, `yield`, and identifiable
  extern calls without a portable unwind contract. The required missing MIR,
  effect, optimizer, and backend primitives are tracked under `doc/08_tracking`.
- Lazy callers now share one blocking Mutex/channel flight and typed completion;
  route keys are canonical and active hits remain no-I/O. Broader concurrency
  across low-level acquire, unload, advice, and other lifecycle APIs is still
  unproved. Production image/signature port binding, imported/indirect unwind
  metadata, leaf-level lease visibility, and executable evidence remain open.
  Status remains `STATUS: FAIL`.

## 2026-08-04 — lifecycle/ABI implementation reconciliation

- Static implementation is complete for the application lifecycle gate,
  prepared prepare/native/finalize split, exact lazy reserve/I/O/commit, facet
  lifecycle transitions, ordinary unload, stable facet/prepared compiler ABI
  leaves, and the injected pack-I/O port contract.
- The runtime owner is below 800 lines; lifecycle source guards pass. These are
  static structure checks, not executable evidence.
- Obsolete blockers claiming a missing typed adapter, prepared backend
  injection, or application dispatcher ABI are superseded.
- Verification remains failed. Open evidence is admitted current-source
  backend/self-host execution and ABI linkage; deterministic concurrency,
  callback-error, stale-commit, and lease-drain evidence; production image/
  signature port deployment and startup configuration; imported/indirect
  unwind plus leaf-level lease visibility; generated manuals, coverage, and
  retained NFR baselines.
- Authoritative status remains `verification-failed` / `STATUS: FAIL`; no
  release, tag, version bump, or main push is authorized.
