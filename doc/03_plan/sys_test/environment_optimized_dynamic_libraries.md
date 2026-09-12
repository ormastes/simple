# System Test Plan: Environment-Optimized Dynamic Libraries

**Status:** Feature A + NFR N2 + target registry B + inspector input 1 selected; contract/admission/binding, host-target planning, and inert GPU completion adapters have focused diagnostic coverage. The executable scaffold has 30 intentionally fail-fast scenarios for REQ-001..016 and NFR-001..010; NFR-011/012 have no executable scenarios yet. Target-registry and atomic-input authority integration remains required until real parser artifacts and provider-backed execution exist.

## Test boundary

Exercise the public catalog/admission/binding and parser-provider seams. Do not infer execution from filenames, configured target flags, loaded symbols, queue admission, or a manifest label. Every positive execution row must bind the admitted artifact digest, provider generation, actual callable/device completion evidence, and normalized output.

## Canonical scenario helpers

- `setup_environment_catalog`: create bounded synthetic environments and digest-addressed candidates.
- `step_admit_variant`: apply compatibility, trust, ABI, dependency, and OS/device-state predicates.
- `step_bind_provider`: publish and pin a generation-scoped typed facet.
- `check_execution_receipt`: distinguish requested, admitted, bound, executed, completed, and retired states.
- `setup_canonical_target_registry`: install a bounded versioned registry fixture with canonical triples and aliases.
- `step_start_atomic_inspector`: start one owned inspector with immutable bounded bytes and concurrent capture limits.
- `check_atomic_inspector_terminal`: require exact write, stdin close, bounded drains, reap, and matching input digest/count.
- Any scenario scaffold without real assertions ends with `fail("environment-optimized provider scenario not implemented")`.

## Requirement-to-scenario matrix

| Coverage | Scenario families | Required oracle |
|---|---|---|
| AC-3/4 | host-target-placement-policy separation; descriptor decoding; dependency closure | Exact typed rejection reason and immutable binding identity |
| AC-5 | startup sealing; hot dispatch; cache invalidation; cancellation and retirement | No hot-path catalog scan/lock; stale generation cannot execute |
| AC-6 | observation, opt-in, parser SIMD, dynlib/JIT/AOT, GPU stages | Later stage cannot promote without predecessor evidence |
| AC-8 CPU | x86 baseline/v2/v3/v4 missing-feature rows, AVX OS state, Arm SVE length, RISC-V vector permission, architecture mismatch | Ineligible code is never opened or called |
| AC-8 parser | legacy/canonical normalized parity, dialects, every vector tail, guard pages, malformed UTF-8, incremental/error recovery | Stable tokens/spans/nodes/diagnostics and independent legacy oracle |
| AC-8 generated code | host-target separation, strict numerics, emitted executable inspection, scalarization reporting | Declared requirements match backend output and observed executed implementation |
| AC-8 GPU | absent device, missing enabled feature, wrong program, device loss, fence absence, cancellation | No device claim without correlated completion and retirement evidence |
| AC-8 NFR | cold/warm startup, p50/p95/p99 request latency, max RSS, mapped text, transfers, artifact size | Retained samples and threshold policy selected by user |
| AC-9 | unavailable OS/ISA/device rows | `blocked` receipt plus linked TODO, owner, resume command, artifacts, reviewer |
| REQ-015 | registered alias equivalence; registry-version/mapping invalidation; unknown, ambiguous, and ABI/object-format mismatch | Canonical tuple and numeric IDs come from one repository-owned registry; mapping version/digest changes every downstream identity; invalid rows fail before cache/publication authority |
| REQ-016 | exact immutable input; empty/maximum boundary; overflow, partial write, digest mismatch, and unreaped process | One owner-issued terminal receipt binds exact input digest/count through write, close, bounded concurrent drains, terminal status, and reap; no early authority token |
| NFR-011 | post-construction canonical lookup and provider hot-path audit | bounded/allocation-free lookup; no network/signature service; no registry access during provider batch execution |
| NFR-012 | empty/maximum input, output backpressure, short-write, overflow, cancellation, timeout, early-exit, and reap-failure matrix | bounded concurrent progress; every failure has an explicit non-authoritative receipt and no live process lease |

## Exact missing production-test manifest

The following files do not yet exist as production-backed tests. They are
required in addition to the intentionally red end-to-end scaffold; focused
unit, fixture, codec, or QEMU evidence cannot substitute for them.

| Workstream | Required executable spec | Exact production cases and evidence | Current state |
|---|---|---|---|
| Shared parser unification | `test/03_system/app/compiler/feature/canonical_parser_provider_parity_spec.spl` | Production `FrontendFacetV1` session vs independent legacy frontend across Simple, SDN, and sosh; valid/malformed Unicode, interpolation, indentation, incremental append/reset, recovery, spans, diagnostics, and opaque AST/HIR boundary; generation cutover/drain. | MISSING |
| GPU parser/offload | `test/03_system/app/compiler/feature/parser_gpu_provider_fence_execution_spec.spl` | Production GPU parser batch submission with admitted enabled features/program/resources; device readback checked against CPU oracle; fence/timestamp completion and buffer/device lease retirement; absent device, missing feature, wrong program, device loss, missing fence, cancellation negative controls. | MISSING |
| SIMD optimization of Simple/parser | `test/03_system/app/compiler/feature/parser_simd_provider_native_execution_spec.spl` | On qualified physical/self-host x86_64 AVX2, map and call the exact admitted parser sibling, compare scalar output over all dialect/tail/guard-page/malformed rows, record emitted/mapped/called/executed facts and no false v3/v4 claim. QEMU-only evidence is blocked. | MISSING |
| Generated JIT/AOT/binary SIMD | `test/03_system/app/compiler/feature/parser_backend_artifact_evidence_spec.spl` | Backend accepts exact target config, emits a parser-only sibling/JIT unit, V3 inspection sees its exact sealed bytes, executable mapping/call output matches scalar, registry mapping/version invalidates cache/plan/receipt, and stale/unknown target rows fail closed. Run native with `SIMPLE_NO_STUB_FALLBACK=1`. | MISSING |

### B + 1 authority integration tests

The checked-in registry unit test and runtime C self-check are necessary but do
not close these production joins:

| Requirement | Required executable spec | Exact gap |
|---|---|---|
| REQ-015 / NFR-011 | `test/02_integration/compiler/driver/canonical_target_registry_consumer_v1_spec.spl` | Consume a live registry token in real target-profile, cache, binding-plan, receipt, and replacement/drain owners; measure post-construction lookup and prove no provider hot-path registry work. |
| REQ-016 / NFR-012 | `test/02_integration/compiler/driver/owned_process_atomic_inspector_v3_spec.spl` | Drive the production Simple opaque V3 adapter with exact input, boundary/backpressure, failure injection, terminal-token gating, tool identity, and no-leak assertions. The C self-check alone is not this evidence. |

Add two fail-fast SSpec scenarios to
`test/03_system/app/compiler/feature/environment_optimized_dynamic_libraries_spec.spl`
before claiming complete requirement coverage: one `# @req NFR-011` hot-path
registry-overhead scenario and one `# @req NFR-012` bounded inspector-progress
and terminal-failure scenario. They remain `FAIL-FAST` until their production
owners and timing/lifecycle oracles exist; their current status is **MISSING
EXECUTABLE SPEC**, not PASS or blocked execution evidence.

## Execution order

1. Canonical target-registry alias, version, and fail-closed fixtures.
2. Contract codec and negative admission fixtures.
3. Deterministic policy and binding-generation tests.
4. Atomic inspector exact-input, boundary, and failure-injection fixtures.
5. Registry-consumer and V3 opaque-adapter integration tests.
6. Native/SMF/JIT callable and cache-identity integration tests.
7. Parser scalar/SIMD differential tests.
8. Current-host emitted-code and performance evidence.
9. External host/device rows, each independently retained.

The first native SIMD execution row reuses
`test/03_system/feature/compiler/x86_avx2_custom_native_execution_spec.spl`.
It is external to the current AArch64 host and remains blocked until an admitted
pure-Simple Stage-4 runner is available on x86_64 with OS-usable AVX2. Its
encoder, mapped-callable result, and scalar oracle must be joined to the exact
artifact inspection receipt before any parser promotion.

Current GPU unit evidence covers exact provider/program/image/device/lease
correlation and preserves `gpu_finished`, `completed`, and `retired` as separate
states. It does not satisfy step 6: installed backends still lack the uniform
submission/fence/timestamp/retirement authority required for real-device proof.

## Completion rule

The executable SSpec and authored manual exist as fail-fast design artifacts,
not PASS evidence. Replace helper `fail(...)` bodies only with production-owner
calls and typed oracles, regenerate the manual, then run each acceptance command
once after convergence. REQ-015 and REQ-016 each require all three focused
scenarios to pass before the selected registry or inspector can authorize cache,
publication, or inspection evidence.

## E1-E5 environment dispatch acceptance handoff — 2026-09-11

This section is the current test-side handoff for the additive
`environment-variant-dispatch-v1` ledger frozen in
`doc/03_plan/agent_tasks/simple_infra_optimization_parallel_plan_2026-09-08.md`.
It does not replace the historical 47-item/800-point ledger and does not infer
implementation status from source presence. The five lanes contain 38
obligations and 100 importance-weighted points; the current state is
`P=0,F=0,E=0,U=38,X=0`, `D=0`, and `D_w=0`. Ratios whose denominator is zero
are `N/A`; all 38 rows remain pending (`U`).

### Canonical E5 executable matrix

| ID | Evidence class | Requirement mapping | Executable SSpec | Generated manual | Current state |
|---|---|---|---|---|---|
| E5-001 | `integration` | REQ-002,003,004,006,010,014 | `test/02_integration/compiler/environment_variant_activation_spec.spl` | `doc/06_spec/test/02_integration/compiler/environment_variant_activation_spec.md` | `U / MissingEvidence` until E1-E3 owner receipts |
| E5-002 | `physical_worker` | REQ-011,012,013 | `test/03_system/runtime/environment_variant_gpu_infrastructure_spec.spl` | `doc/06_spec/test/03_system/runtime/environment_variant_gpu_infrastructure_spec.md` | `U / MissingEvidence` until E4 device receipts |
| E5-003 | `integration`, `performance` | REQ-013,014 | `test/03_system/app/compiler/feature/environment_variant_activation_spec.spl` | `doc/06_spec/test/03_system/app/compiler/feature/environment_variant_activation_spec.md` | `U / MissingEvidence` until qualified runner/reviewer |
| E5-004 | `source_contract` + `integration` | REQ-002,011,014 | `test/03_system/app/compiler/feature/environment_variant_activation_spec.spl` | same as E5-003 | `U / MissingEvidence` until canonical row authority |

Every visible scenario retains its stable ID and the frozen suffix
`[importance=critical|high; importance_weight=3|2]`. The test-side helper names
are frozen as `collect_policy_sources`, `resolve_policy_and_ceiling`,
`probe_execution_domain`, `admit_exact_provider`, `pin_selected_generation`,
`execute_bounded_region`, `validate_completion_receipt`, and
`drain_and_retire`. Missing owners fail explicitly with `MissingEvidence:<ID>`;
they are not opt-in skips, tautological passes, fixture substitutions, or
claims of GPU/native execution.

### Pending lane summary

| Lane | Obligations | Weight | State | Blocking authority |
|---|---:|---:|---|---|
| E1 policy-source acquisition | 8 | 20 | `U` | presence-preserving source owner and authenticated admin restrictions |
| E2 live x86 admission | 9 | 25 | `U` | trusted CPUID/OS-state/affinity snapshot and exact artifact admission |
| E3 startup binding/lifetime | 9 | 25 | `U` | private package activation, source sessions, drain/retry owner |
| E4 GPU task infrastructure | 8 | 20 | `U` | owner-issued submit/fence/readback/cancel/retire and native lock safety |
| E5 integrated evidence/tracking | 4 | 10 | `U` | qualified runner, retained receipts, manual review, canonical row allocator |
| **Total** | **38** | **100** | **U** | no admitted execution or deployment evidence |

### Astra final review guide

Astra accepts this handoff only after checking the isolated diff against the
frozen E1-E5 manifest and exact base/head revisions. The review must confirm:

1. E5 owns only test, manual, instrumentation, and canonical tracking edits;
   no production activation, provider deployment, or default-selection change
   is hidden in the acceptance diff.
2. Each E5 ID maps to the exact requirement IDs and evidence class above;
   split implementation/review ownership remains many-to-many without adding
   accounting weight.
3. `MissingEvidence` names the absent production owner and a concrete resume
   condition. Source inventories, catalog enumeration, scalar fallback,
   generated GPU artifacts, routing, or a successful test process do not close
   `physical_worker` or native execution rows.
4. GPU evidence separately proves submission, fence/completion/readback, and
   retirement. Parser-GPU availability remains false until the device receipt
   exists; CPU/model/QEMU fixtures cannot substitute for it.
5. Importance tags are review priority only. No tag, scenario count, manual,
   or source review changes the 0/100 pending ledger. A row becomes `P` only
   after all mandatory leaves and the independent issuer/runtime/reviewer
   receipt are retained.
6. All three changed SSpecs regenerate successfully with zero stubs, visible
   operator steps, folded executable source, and no executable `.spl` under
   `doc/06_spec`. A qualified native runner is still required for execution;
   interpreter loading or docgen success is not runtime admission.

The next handoff is an exact immutable E1-E4 revision manifest. Until it names
the production owners, runner, issuer, artifact, and reviewer receipts, this
E5 suite remains intentionally RED/`MissingEvidence` and the lane ledger stays
`U`.
