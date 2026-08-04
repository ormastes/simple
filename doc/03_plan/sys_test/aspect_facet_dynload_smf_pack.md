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

## Callback-safe advice and lifecycle concurrency

### Deterministic unit acceptance

These scenarios require no threads or native callback execution and already
have real API seams:

| Scenario | Owner/API | Executable oracle |
|---|---|---|
| Complete phase chain pins exact generations before invocation and releases all tokens afterward | `advice_binding_registry.spl:advice_dispatch_projection_with_invoker` | `advice_binding_registry_spec.spl` asserts ordered values `[3003, 2002, 1001]`, three acquisitions, three releases, and final pin count zero |
| Stale second projection entry releases the successfully acquired first token | Same | Fatal outcome identifies stale/unpublished generation; acquired and released counts are both one; pin count is zero |
| Loader-owner validation and callback failure release every acquired token | Same | Both failure paths report two acquired/two released and exact-generation pin count zero |
| Visibility disappears before lifecycle quiesce | `advice_dispatch_projection_invalidate`, `LifecycleManager.quiesce_generation_for` | Projection has zero entries while generation remains active, then transitions to `quiescing` |
| A held canonical lease prevents ordinary unload completion | `AspectApplicationRuntime.unload_published_aspect` | `aspect_application_runtime_spec.spl` observes first result `quiescing`, no new acquisition, then `unloaded` only after exact lease release |
| Same-route activation shares one result; different routes serialize | `AspectLazySingleFlight` | `aspect_lazy_singleflight_spec.spl` asserts owner/follower roles, shared typed failure, wake semantics, and rejected follower completion |

Do not duplicate these with source-text assertions. Their current unit specs call
the real registry, lifecycle, runtime, and single-flight APIs.

### Callback overlap system acceptance

Actual callback-vs-unload overlap is not deterministic through the current test
invoker: `advice_dispatch_projection_with_invoker` accepts only
`fn(i64) -> Result<i64, text>`, so the callback cannot observe the pinned
`LifecycleManager`, announce that invocation began, or wait on a test barrier.
A global fake lifecycle would inspect a different immutable snapshot and is not
valid evidence.

Owner: `src/compiler/99.loader/loader/advice_binding_registry.spl` together
with the application capsule in
`src/app/startup/aspect_application_runtime.spl`. The production callback ABI
must remain unchanged. Add a test observer/barrier seam around the production
pin/invoke/release phases, not inside the native witness ABI.

Required system spec:
`test/03_system/app/simple/aspect_advice_lifecycle_concurrency_spec.spl`.
It must use these visible steps:

1. `step("Publish one exact advice generation")`
2. `step("Pause an admitted callback after its generation pin")`
3. `step("Request unload while the callback remains pinned")`
4. `step("Release the callback and drain the generation")`
5. `step("Reject dispatch through the retired projection")`

Exact oracles:

- callback entry is observed once and exact-generation pin count is one;
- unload removes projection/facet visibility and returns `quiescing` without
  reclaiming the loader-owned witness;
- a new dispatch is rejected while the already-entered callback remains valid;
- callback completion releases exactly one token, after which unload returns
  `unloaded` and cache/provider ownership disappears;
- callback error follows the same drain sequence and returns its typed E-AF010
  failure without leaking a token;
- two application capsules with equal slot IDs never share projections, tokens,
  barriers, lifecycle counters, or unload state.

This scenario requires real scheduler/barrier execution. A sequential mock,
sleep-based race, or manually acquired token cannot satisfy callback-overlap
acceptance.

## Portable unwind metadata acceptance

The common `MirCallUnwindContract` metadata API now exists. Static unit evidence
covers its required field, deterministic JSON spelling/order, contradictory
contract/edge rejection, preservation through representative optimizer and
backend consumers, and fail-closed indirect calls while a facet lease may be
live. This is implementation-shape evidence only: no compiler or backend was
executed in the static-only pass. The authoritative remaining gap and owner matrix is
`doc/08_tracking/bug/facet_descriptor_cleanup_unwind_primitives_2026-08-04.md`.

### Deterministic unit specs after the API lands

| Planned spec | Real API exercised | Required oracle |
|---|---|---|
| `test/01_unit/compiler/mir/mir_call_unwind_contract_source_spec.spl`, `mir_call_unwind_json_spec.spl` | `MirTerminator.CallTerminator`, validation, MIR JSON serialization | **Static implemented:** required explicit contract, contradictory pair rejection, deterministic `NoUnwind`/`MayUnwind` JSON; executable round-trip remains pending |
| `test/01_unit/compiler/mir_opt/mir_call_unwind_optimizer_preservation_spec.spl` plus source consumers | SSA, DCE, copy propagation, LICM, inlining, outlining, auto-vectorization | **Static partially implemented:** consumers accept the field and reconstructing passes preserve it; executable all-pass successor preservation remains pending |
| `test/01_unit/compiler/hir/hir_unwind_effect_contract_spec.spl` plus type/semantics source specs | Source attributes, `HirFunction.effects`, function-type effects, callable registration/resolution | **Static implemented:** declarations default to `NoUnwind`; explicit effects are typed and preserved through imports, methods, and call inference; executable parser/import/method tests remain pending |
| `test/01_unit/compiler/mir/facet_member_unwind_contract_spec.spl` | Typed facet witness planning and MIR member-call lowering | Declared facet method effect reaches the emitted indirect call; absent/ambiguous effect is fatal |
| `test/01_unit/compiler/mir/hir_mir_unwind_admission_spec.spl` | HIR-effect to MIR-call admission | **Static implemented:** `NoUnwind` maps to the MIR contract and is admitted; `MayUnwind`, missing, and conflicting metadata are rejected before direct/indirect/method call emission when no cleanup successor exists; a live facet scope retains `E-AF007` precedence |
| `test/01_unit/compiler/mir/facet_cleanup_scope_spec.spl`, `mir_throw_resume_acceptance_spec.spl` | HIR `throw`, `MirTerminator.Throw`/`Resume`, lexical facet cleanup | **Static implemented:** a direct leased `throw` emits each nested release once in reverse order before `Throw`; builder/JSON shape is deterministic |
| `test/01_unit/compiler/mir/mir_call_cleanup_successor_spec.spl` | Future `MayUnwind` call cleanup-successor builder | A call with two live leases creates one unwind successor, releases inner then outer exactly once, preserves the normal successor without early release, and rejects missing/conflicting payload ownership |
| `test/01_unit/compiler/mir/mir_exception_payload_resume_spec.spl` | Future landing-pad payload and `Resume` lowering | The exact thrown exception payload enters the cleanup pad, survives both releases unchanged, and is the operand of exactly one `Resume`; cleanup values cannot replace or alias it |
| backend unwind rejection specs and backend consumer source | Backend admission | **Static implemented:** unsupported Throw/Resume paths reject with `E-MIR-UNWIND002`; executable backend admission evidence remains pending |
| `test/01_unit/compiler/backend/llvm_unwind_contract_spec.spl` | LLVM lowering | `MayUnwind` produces `invoke`; unwind destination owns a valid personality/landing pad, cleanup releases precede `resume` of the original payload, normal destination stays ordinary, and the function has no contradictory `nounwind` |
| `test/01_unit/compiler/semantics/foreign_unwind_source_contract_spec.spl` | Source/HIR function effects | Extern with no explicit contract is rejected in a leased scope; explicit `NoUnwind` is admitted; `MayUnwind` requires cleanup capability |

### Runtime-required system acceptance

`test/03_system/compiler/facet_unwind_cleanup_spec.spl` must run only on a
backend admitted for canonical unwind cleanup. It must call a real foreign or
language callee that unwinds after two nested facet acquisitions, observe
reverse releases for the exact descriptor generations, enter the handler once,
and prove the normal-return sibling path also releases once. Native targets that
still reject unwind edges remain a tested fatal matrix row, not skipped cases.
An aborting `panic` is a separate scenario and must never be presented as
resumable-unwind evidence.

The system spec must include four explicit scenarios: successful normal return;
foreign/language `MayUnwind` with two nested leases and exact payload caught by
the handler; rethrow/resume preserving that payload after reverse cleanup; and
the backend matrix where unsupported targets fail with `E-MIR-UNWIND002`
before code generation. Each scenario must assert exact release counts and
generation identities, not only control-flow completion.
