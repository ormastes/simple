# Environment-Optimized Dynamic Libraries — Staged Plan

Current four-lane implementation truth is tracked in
`doc/09_report/compiler/simple_parser_simd_gpu_jit_four_lane_status_2026-09-08.md`.
That report is the status authority for shared parsing, GPU parser execution,
Simple-native SIMD, and generated JIT/AOT/native SIMD; source presence alone
does not close a lane.

## Status

**Selected pilot:** Feature A (catalog-selected sibling artifacts) with NFR N2
(balanced production performance). Implementation may proceed in staged slices;
no default selection or ABI publication occurs before its focused gates pass.

## Status update 2026-10-25 (verified against `origin/release/1.0.0` @ `57a129fb2b9`)

Seven-plan item 1 status, per source presence plus git log. Source presence is
not acceptance; no host is certified by this note.

| Area | Status | Evidence |
|---|---|---|
| Contracts (`ParserProviderV1`, `EnvironmentSnapshotV1`, `VariantDescriptorV1`, `BindingPlanV1`, `FrontendFacetV1`, `StartupPlanV1`, `ProcessLaunchSpecV1`, SimpleOS image manifest, release evidence) | DONE (source-landed) | `src/compiler/00.common/structural_contracts/environment_variant_*`, `src/lib/nogc_sync_mut/composition/environment_variants/`, `src/app/startup/contract/startup_plan_v1.spl`, `src/lib/common/contracts/execution/{process_launch_spec_v1,simpleos_image_manifest_v1}.spl` |
| Shared parser ownership / parity across compiler, interpreter, tooling | PARTIAL | `ParserProviderV1` dispatch exists; legacy provider is still the only executable one; `FlatAstBridge` migration open (bug trail `6c70e0ecef9`, `f938c3d00a6`) |
| Environment-optimized provider selection, ABI validation, fallback, cache invalidation | PARTIAL | contracts + selector landed; system spec `test/03_system/app/compiler/feature/environment_optimized_dynamic_libraries_spec.spl` still carries `fail(...)`/pending bodies (41 sites) |
| Compile-mode dynload (per-module dynlibs, import library) | OPEN | `doc/08_tracking/bug/dynload_mode_emits_no_per_module_dynlibs_2026-10-24.md` (`507a75ce07a`); per-dynlib receipt record PR #4426 |
| Immutable release candidates + per-host release/bootstrap execution | OPEN | release-evidence producer stopped after third rejected review; no admitted per-host receipts under `doc/03_plan/evidence/seven_plans/` for item 1 beyond Windows frozen-path parity (`windows/item1_frozen_path_2026-09-29.md`) |
| Claimed SimpleOS target boot | OPEN for item 1 acceptance | umbrella scaffold `test/03_system/seven_items_pending/item01_platform_spec.spl` (last touched `0f20291900b`, 2026-10-03) remains NOT_IMPLEMENTED |

Done gate (umbrella §1) is **not met**.

## Authoritative inputs

- Research: `doc/01_research/compiler/simd/simple_environment_optimized_dynamic_libraries_2026-09-07.md`
- Architecture: `doc/04_architecture/compiler/environment_optimized_dynamic_libraries.md`
- Detail design: `doc/05_design/compiler/environment_optimized_dynamic_libraries.md`
- Final feature/NFR requirements:
  `doc/02_requirements/feature/environment_optimized_dynamic_libraries.md` and
  `doc/02_requirements/nfr/environment_optimized_dynamic_libraries.md`

Canonical interface names are `EnvironmentSnapshotV1`, `VariantDescriptorV1`,
`BindingPlanV1`, and `FrontendFacetV1`. Test helpers are
`setup_environment_catalog`, `step_admit_variant`, `step_bind_provider`, and
`check_execution_receipt`. Unimplemented helpers must `fail(...)`.

## Stop gates

- Do not publish V1 ABI or change production defaults before requirements are
  selected and ABI review passes.
- Do not call a provider SIMD without emitted/executed instruction evidence.
- Do not call a GPU path executed without actual submission and completion.
- Do not remove the legacy CPU frontend before independent parity criteria are
  met; current intent is to retain it permanently as an oracle.
- Run each acceptance gate at most once per session and cap verify/fix cycles at
  three.

## Stage 0 — requirements and evidence baseline

1. Produce feature/NFR option documents from the saved research, each option
   with pros, cons, and effort.
2. Ask the user to select; delete unchosen options and write final REQ-NNN/NFR
   files.
3. Trace production callers of current SIMD tier/manifest/probe helpers,
   composition generations, frontend entrypoints, GPU loader, and packed queue.
4. Record reproducible baseline build/test, CPU-only startup latency/max RSS,
   parser workloads, mapped text, and device-path negative controls.

Exit: selected requirements, traceability skeleton, and truthful implemented/
scaffold/stub matrix exist.

## Stage 1 — common contracts and exact environment model

Add versioned bounded schemas/codecs for the four canonical contracts, stable
feature IDs, CPU architecture predicates, vector-state contracts, placement,
reason codes, and receipts. Preserve existing V1 wire records through adapters.
Consolidate platform probes behind one environment authority; do not add a third
CPU feature detector.

Exit: malformed/unknown/overflowing records fail; x86 baseline/v2/v3/v4 missing
features, cross-architecture requests, AVX OS state, SVE length, RISC-V vector
permission, and restricted execution domains are tested.

## Stage 2 — catalog admission and generation binding

Implement bounded catalog loading, dependency locks, eligibility-before-ranking,
`prefer`/`require`/`max`, inert metadata verification, loader adapters, immutable
`BindingPlanV1`, generation pins, quarantine, and explain receipts. Reuse current
composition provider-generation ownership.

Exit: identical inputs select deterministically; constructor-bearing rejected
candidates are not loaded; native and SMF placements expose the same logical
contract with distinct truthful callability states; hot dispatch is dense and
allocation/lock/free of catalog work.

## Stage 3 — legacy frontend seam

Insert `FrontendFacetV1` behind the shared frontend facade through a legacy
adapter. Preserve reset, append, isolated error state, interpolation,
placeholder transforms, diagnostic order, spans, compiler, interpreter, and
REPL behavior. Default remains legacy.

Exit: reference-mode existing tests are unchanged, session generation is pinned,
and forced unavailable/incompatible providers fail according to selected policy.

## Stage 4 — canonical scalar parser parity

Qualify generated grammar/action programs for selected Simple, SDN, and sosh
dialect scope. Use flat arenas, deterministic count/scan/reserve/emit, private
staging, typed CPU work tags, and normalized oracle comparisons. Incomplete
dialect coverage cannot become default.

Exit: selected valid, malformed, incremental, recovery, Unicode, indentation,
string/interpolation/custom-block, and facade acceptance matrix passes.

## Stage 5 — pure-Simple SIMD parser family

Implement baseline, x86-64-v3, x86-64-v4, separately gated optional byte-feature,
and selected Arm/RISC-V kernels through existing MIR/backend vector lowering.
Cover every tail length, guard-page boundary, chunk state, alias/dependence, and
strict numerical rule. Build only parser variants and necessary private helpers.

Exit: exact cross-variant results, actual artifact ISA boundaries, emitted and
executed vector evidence, parser-only rebuild scope, and same-machine AVX2/
AVX512 measurements meet selected NFRs.

## Stage 6 — generated dynlib and JIT/AOT specialization

Separate host environment from `TargetCodegenProfile`; build baseline facades and
selected sibling libraries; bind exact backend-accepted features, ABI/numerics,
dependencies, and provider identity into caches/receipts. Prevent LTO/init/deps
from contaminating the baseline closure. Treat SMF native payloads with the same
target predicates and stronger execution-state evidence.

Exit: baseline host can cross-compile but not execute an incompatible target;
facade remains baseline-safe; stale/incompatible caches miss; strict unsupported
features fail rather than silently scalarize under a SIMD label.

## Stage 6A — backend-owned target evidence producer

Implement this independently of unresolved numeric target-ID mapping. The
backend/build owner must accept exact requested features, hash emitted executable
bytes and dependency closure, inspect those exact bytes once, invoke a pinned
callable only on a compatible execution domain, compare its output with the
scalar oracle, and advance the existing target receipt only while every resource
identity remains correlated. Inspection binds tool and normalized output;
execution binds environment, callable, input, output, invocation count, and
terminal retirement.

Exit: production APIs accept no freely invented evidence digest; substituted
artifact/tool/output/callable/environment facts fail; baseline loader/init/
dependency closures contain no forbidden ISA; optimized artifacts prove both
emitted and actually executed instructions.

The canonical first implementation is `ParserBackendTargetEvidenceOwnerV1`,
with opaque build, inspection, and execution tokens and explicit Built →
BytesSealed → Inspected → ExecutedAndRetired stages. It consumes live planner,
emission, authenticated backend, sealed publication/generation, mapping,
affinity, and capability authorities. Its final digest binds owner-private
adapter/buffer/pin correlations plus separate requested, accepted, declared,
observed, and executed features. It inspects the parser lexical classifier;
the existing f32x8 AVX2 proof is a different route and cannot satisfy this gate.

## Stage 7 — existing GPU registry adapter and truthful completion

Adapt admitted host/device artifact identities into the existing GPU registry.
Add enabled-feature, limit, layout, memory-domain, program, fence, and retirement
receipts. Connect the current packed DrawIR epoch path to actual provider
submission and completion without redesigning the queue.

Exit: device absent/wrong program/missing feature/provider failure/no fence/device
loss negative controls fail correctly; actual output and fence retire pinned
resources; CPU-only paths initialize no GPU state.

## Stage 8 — frontend and resident execution islands

Add GPU lexical/structural/grammar/local-semantic batches with private staging
and explicit CPU global-binding/recovery handoffs. Add a residency-aware planner
shared with compute/render/scene facets and bounded fairness between interactive
rendering and compiler batches. Preserve conservative rendering and GPU-owned
scene profiles as distinct products.

Exit: end-to-end costs include transfer/synchronization; required scene profiles
never silently execute CPU semantics; visible results are deterministic; compile
work cannot starve interactive queues.

## Stage 9 — automatic promotion and production rollout

Begin observation-only, then explicit opt-in, then qualified automatic parser
selection, generated-code adoption, and independently qualified GPU profiles.
Install calibration evidence explicitly; never benchmark invisibly at startup.
Support per-artifact/environment quarantine and new-session rollback.

Exit: every selection, fallback, rejection, cache identity, and executed backend
is explainable; all selected requirements and NFRs have direct test/evidence
coverage; verify reports PASS before release work begins.

## Ownership and parallel lanes

| Lane | Owner | Scope | Dependencies |
|---|---|---|---|
| Contract | highest-capability architecture lead | canonical names, schemas, feature IDs, ABI/version/reason policy | Stage 0 |
| Host probes | platform expert | exact CPU/OS/device usable-state adapters | Contract |
| Composition | loader/composition expert | catalog, eligibility, dependencies, binding, lifecycle | Contract, probes |
| Frontend | parser expert | legacy seam, scalar parity, SIMD/GPU executor adapters | Composition |
| Codegen | compiler/backend expert | target separation, lowering, dynlib/JIT/AOT evidence | Contract |
| GPU | GPU/runtime expert | registry adapter, programs, fences, leases, resident planner | Composition |
| Render/scene | UI/render expert | packed queue and semantic profiles | GPU |
| Verification | independent normal/highest-capability reviewer | differential, failure, hardware, perf, docs | all stages incrementally |

Lower-model sidecars may inventory callers, draft synthetic fixture matrices,
and collect documentation evidence. They may not define or change the canonical
interfaces, accept generated-manual quality, waive exclusions, or mark stages
done. Merge owner: contract/architecture lead. Final reviewer: independent best
available normal/highest-capability model.

## Test and documentation work

After final REQ-NNN selection, create a system-test plan and executable SPipe
spec in the canonical mirrored paths, then generate its manual. Primary scenarios
use the frozen setup/step/checker helpers; detailed architecture/feature/hardware
matrices may be folded. Built-in matchers only. Every placeholder fails fast.
The manual must explain the operator flow without exposing raw fixture mechanics.

Update user/configuration guides only when accepted CLI/config syntax is
implemented. Keep all proposed examples labeled until then. Verify no executable
spec is placed under `doc/06_spec`.

## Required final evidence

- selected REQ-NNN and NFR traceability with no missing coverage;
- exact environment and override negative matrix;
- native/SMF/static/JIT callability and execution-state distinctions;
- legacy and canonical parser differential results for declared dialect scope;
- emitted and executed SIMD evidence, not target flags alone;
- actual GPU submission/fence/readback and lease retirement;
- host-target separation and cache invalidation proofs;
- cold/warm startup, representative latency, p95/p99, max RSS, mapped text,
  transfers, synchronization, and CPU service time against selected budgets;
- direct environment/process facade audits and required compiler/lib/MCP smoke
  gates for any affected source scope.

## Explicit non-goals for the initial parser pilot

- a whole-executable matrix for every CPU/GPU combination;
- replacing the existing GPU registry, SimpleRing, Object VM, SOSIX, or DrawIR;
- full GPU browser semantics before parser qualification;
- per-token dynamic dispatch or hidden startup compilation;
- arbitrary aspect interception as provider substitution;
- claiming every AVX-512 extension from AVX512F or fixed-width SVE universally.

## Four-workstream implementation truth table (2026-09-08)

| Workstream | Current evidence | Status | Next promotion gate |
|---|---|---|---|
| Shared parser unification | Legacy frontend remains the oracle; a frontend-owned lazy advisory seam, scalar lexical summaries, and a 22-state transition-table foundation exist. Canonical Simple/SDN/sosh grammar parity and full parser replacement do not. | Foundation implemented; unification incomplete | Differential dialect, malformed-input, incremental, interpolation, indentation, and facade parity |
| GPU parser/offload | Generic provider/device contracts and owner-scoped packed proof/callback schemas exist. The hosted native ABI now authenticates an exact sealed Linux provider image, issues unguessable bounded session/resource/completion capabilities, pins calls and generations through fence/readback, stages and checksums output before commit, and blocks unload until retained owners drain. No packed parser batch is connected to this substrate; compatibility completion remains routing-only. | Native provider substrate implemented; parser integration incomplete | Authenticated device-program image owner, task-owner bridge, Vulkan parser kernel, physical device readback, and negative control |
| SIMD optimization of Simple/parser | An authenticated x86-64 SysV AVX2 32-byte equality primitive and lexical mask batch exist; exact bytes executed under QEMU TCG. Scalar code still owns lexical-state resolution; native hardware, Win64, v4, and full-parser execution remain open. | Narrow SIMD kernel implemented; product optimization incomplete | Physical/self-host execution, full ABI/artifact receipts, parity, parser-only packaging, and NFR speedup |
| Generated JIT/AOT/binary SIMD | Target-codegen contracts and a parser variant build plan separate host and target. Existing AOT is whole-module; parser sibling emission, target-aware JIT materialization, cache V2 implementation, and emitted/executed ISA proof are missing. Native callable release also leaves stale copies able to invoke an unloaded mapping (see `doc/08_tracking/bug/environment_variant_callable_release_lifetime_2026-09-26.md`). | Design/contracts in progress | Cache V2 validation, actual sibling artifacts/JIT units, disassembly/metadata checks, callable execution, rollback, and unique mapping lifetime/revocation evidence |

None of the four workstreams is complete. The native GPU substrate is not a
parser-execution claim: `FRONTEND_OFFLOAD_GPU_PARSE_AVAILABLE` remains false.
Linux admission requires the backend provider path and its exact configured
SHA-256; non-Linux authenticated table admission remains fail-closed until an
immutable mapped-byte primitive exists. The immediate independent units are
the device-program/task bridge and cache V2 canonical validation.

## Stage 7A — Vulkan retained packed completion adapter (planned, not admitted)

This is the next bounded GPU unit under Stage 7. It connects the existing
packed DrawIR epoch seam to a real Vulkan provider without redesigning the
queue, registry, or `Engine2dGpuEpochReceipt`. The current compatibility
completion remains routing-only and must not be promoted by this plan.

### Owner boundaries

| Owner | Exact responsibility | Must not do |
|---|---|---|
| Rust Vulkan runtime | `rt_vulkan_submit_no_wait` accepts the command and transfers command, fence, and native owners into `VulkanState` quarantine; `rt_vulkan_wait_fence` observes that handle; a new targeted reap operation should free the signalled quarantined command/fence/owners and record handle retirement | Do not let Simple free a submitted command or native fence; `rt_vulkan_destroy_fence` currently revokes a handle but is not sufficient targeted reap for a quarantined submission |
| No-GC Simple Vulkan SFFI | Owns the typed provider/session/device identity, immutable dependency-retain record, fence handle bookkeeping, bounded readback call, and fail-closed error/quarantine orchestration | Do not inspect Vulkan objects or claim completion from a packet counter; release descriptor/buffer/pipeline/shader only after Rust reap |
| Packed DrawIR queue | Owns request/epoch/queue generations, ring payload lease, content checksum, and parent-authoritative receipt transition | Do not call raw Vulkan FFI directly, infer device completion from `complete_pending`, or release the payload before the provider retirement proof |
| Environment/composite bridge | Correlates provider/variant/artifact, plan/environment generations, lease/content identity, fence identity, readback checksum, and retirement into the existing receipt | Do not become a second queue, registry, scheduler, or native lifetime owner |

The existing Rust paths are `rt_vulkan_submit_no_wait` and
`rt_vulkan_wait_fence` in `src/compiler_rust/runtime/src/vulkan_graphics_runtime_compute.rs`
and `VulkanState::clean_quarantined_compute` in
`src/compiler_rust/runtime/src/vulkan_graphics_runtime_core.rs`. The existing
Simple boundary is `src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl`.
`clean_quarantined_compute` is currently reached by `rt_vulkan_wait_idle`,
which is a device-wide fallback rather than a fence-scoped reap; Stage 7A must
add or expose a targeted Rust reap after successful wait before it can claim
per-submission retirement.

### Required submit → wait → reap ordering

1. Queue admission validates the immutable request, payload lease, provider
   generation, queue/backend handle, and bounded packet bytes. The Simple
   provider adapter retains all native dependencies and the payload lease before
   submission.
2. The adapter calls `rt_vulkan_submit_no_wait`. A positive fence handle is the
   only accepted submitted state. `0` is submit failure; `-1` is unknown
   completion and enters quarantine/recovery. After positive submission, Rust
   owns the command and native owners; Simple owns only its retain record.
3. The adapter calls `rt_vulkan_wait_fence(fence, timeout_ns)`. A timeout or
   wait failure leaves the fence, command, native owners, dependencies, and
   payload lease retained. It must not call the ordinary free path.
4. After a successful wait, the adapter performs bounded provider readback and
   the required negative control, then constructs provider-issued evidence
   containing fence identity, provider/device/driver identity, queue/session
   generations, content/lease joins, host/device completion facts, and a
   nonzero readback checksum.
5. Only after evidence validation does it call the targeted Rust reap. Reap
   frees the quarantined native command/fence/owners exactly once. Calling
   `rt_vulkan_destroy_fence` before targeted reap is not a substitute: current
   Rust treats a quarantined handle as revocation while quarantine retains the
   fence and command until cleanup.
6. After targeted Rust reap succeeds, Simple releases its dependency-retain
   record and reports retirement. The queue then advances the parent-owned
   receipt through `GPU_FINISHED` and `COMPLETED`; only the same proof may
   advance `RETIRED` and release the payload lease.

### Staged implementation and gates

- **7A.1 Rust targeted reap:** add a fence-handle lookup/removal operation that
  succeeds only for a known signalled quarantined submission, is idempotently
  rejected after retirement, and never frees an unsignalled command. Add
  non-Vulkan `0`/unsupported behavior without changing the existing idle
  recovery path.
- **7A.2 Simple retained adapter:** add a bounded record keyed by fence,
  provider/session generation, payload lease, content checksum, and dependency
  handles. Route no-wait submit, wait, readback/evidence, targeted reap, then
  dependency release through one owner function. Unknown completion retains the
  record and uses existing idle recovery only as an explicit fallback.
- **7A.3 Queue/bridge join:** replace the compatibility completion's
  `engine2d_gpu_device_evidence_none()` only for an admitted retained provider
  record. Preserve CPU fallback and routing-only receipts when any proof field
  is absent or mismatched.
- **7A.4 Qualification:** run one focused physical-device lane covering exact
  CPU-oracle/readback parity, fence timeout/device-loss recovery, duplicate or
  stale fence, changed payload checksum, wrong provider/session generation,
  release-before-reap, and repeated retirement. No QEMU/emulator result may be
  labeled physical-device evidence.

The promotion gate is a real provider-issued fence plus exact readback and
lease-retirement evidence. Until 7A.1–7A.3 exist, the current queue TODOs in
`draw_ir_runtime_queue.spl` remain truthful routing-only safeguards.
### Stage 6A.1 — backend-issued acceptance envelope

1. Extend the admitted backend session compile result with an opaque generation-
   scoped token and exact object-byte projection.
2. Bind provider/session generation, backend implementation digest, normalized
   target/options, requested and explicitly accepted feature sets, result kind,
   byte digest/count, and terminal status.
3. Adapt builtin LLVM and Cranelift object producers at their common session
   boundary; do not issue from `backend_feature_authority_v1`.
4. Permit the parser evidence owner to advance only from a live matching token.
5. Test substitution, revoked session, unsupported requested feature, changed
   bytes, and release ordering. Keep inspection and execution stages closed.

Prerequisite split:

- 6A.1a: owner-issued backend-session generation and compile-use lifetime.
- 6A.1b: versioned result envelope with explicit accepted features; V1 maps to
  unknown and cannot satisfy strict SIMD evidence.
- 6A.1c: builtin LLVM/Cranelift producers report backend-confirmed acceptance.
- 6A.1d: parser evidence owner consumes the live token and exact bytes.

### Historical mainline source audit (2026-09-28)

At `origin/main` commit `3e9bc64d6bf`, the Stage 6A.1 acceptance envelope is
not present in the checked-in source.
`src/compiler/70.backend/backend_plugin/session.spl` still exposes the V1
`BackendSession` and its ordinary `CodegenOutput`/`CompiledModule` results;
`src/compiler/70.backend/backend_plugin/loader.spl` returns that raw session.
The builtin adapter reads the request target and optimization, but its
constructor does not carry `BackendPluginRequestV1.features` into an owned
target context or return backend-confirmed accepted features. No
`BackendPluginTargetContextV2`,
`AcceptedExact` result, or `ParserBackendTargetEvidenceOwnerV1` definition is
present under `src/` at this commit.

The “Implemented checkpoint” paragraphs below are not verified by this pinned
mainline source. Treat 6A.1a–d as open on main: first land an owner-issued
session generation and compile-use lifetime, then the V2 result envelope,
backend-confirmed LLVM/Cranelift
configuration, and a live-token parser evidence join. Recheck this audit after
each merge before advancing inspection or execution claims.

### Current mainline source audit (2026-09-28)

At `origin/main` commit `980f32987c7`, Stage 6A.1 has moved past the
historical audit above. The backend plugin's `session_authority_v2.spl` now
owns session generations, compile-use tokens,
retained module/AOT object bytes, byte digests, result tokens, and release
ordering. The V1 backend result projection explicitly reports feature
acceptance as `Unknown`. This is source implementation of the 6A.1a/b
ownership boundary; executable qualification remains pending.

`BuiltinBackendTargetContextV2` exists in `target_context_v2.spl` and the
builtin adapter retains it, but feature-bearing requests still refuse before
emission. The presence of the `AcceptedExact` enum case does not prove an
issued backend-confirmed acceptance record. No production
`ParserBackendTargetEvidenceOwnerV1` was found at this commit, so 6A.1c/d
remain open. `parser_external_inspection_tool_owner_v1.spl` still returns
`ProcessPortUnavailable` from start and `InspectionAuthorityBlocked` from
the join. Complete inspection and callable execution remain unqualified.

The draft loader, builtin LLVM, and partial ELF inspection checkpoint
paragraphs below describe intended transitions. They do not override this
pinned mainline audit or constitute production acceptance evidence.

Draft checkpoint: the strict loader-to-owner path and real builtin LLVM
object producer now issue V2 `Unknown` evidence with exact byte lifetime. This
does not satisfy 6A.1c confirmation; the next gate is backend-authored LLVM
accepted-feature output from target-machine configuration.

6A.1c begins with propagation, not receipt issuance: carry normalized request
CPU/features through builtin adapter construction into LLVM/LLVM-lib target
configuration, reject unsupported features before emission, and return the
effective configuration alongside the exact bytes. Only then may the result
owner convert Unknown to AcceptedExact.

Draft checkpoint: builtin LLVM compiles through its retained exact
plugin target context and returns effective CPU/features with exact bytes. The
session authority issues AcceptedExact only when those canonical features equal
the request. This completes LLVM configuration acceptance, not instruction
inspection or execution. Cranelift and dynamic V1 remain Unknown.

Cranelift V2 provider work in this draft adds a strict hosted ISA constructor,
reads optimization and canonical x86 feature flags from the same live ISA used
by `ObjectModule`, and rejects unsupported CPU/optimization/feature requests.
Feature readback checks Cranelift's effective AVX2/FMA/SSE4.2 prerequisites;
O1/Basic and O3/Aggressive remain rejected because this Cranelift version has
no distinct matching optimization mode.
The retained builtin adapter uses that constructor for admitted Cranelift
compiles. The session authority still rejects feature-bearing requests and
projects Cranelift results as `Unknown`: it does not yet retain a provider-owned
accepted-feature record with the exact object bytes. This is a 6A.1c input,
not completion of 6A.1c or emitted/executed SIMD evidence.

Draft inspection checkpoint: a bounded strict x86-64 ELF64 ET_REL
decoder projects exact ordered `.text`/`.text.*` candidate sections with
per-section and framed projection digests. It rejects malformed identity,
string tables, ranges, overlaps, and resource excess. This is intentionally not
the complete executable closure or SIMD instruction/execution evidence. The
parser evidence owner now issues an intermediate `Inspected` transition over
its retained exact bytes and the registered pure-decoder identity, with
recomputed framed evidence and deep-copied rows. Production promotion still
requires an identity-bound external tool owner for complete executable-section
and relocation-aware inspection; arbitrary compiler output must not be promoted
using a partial home-grown instruction decoder.

6A.2 external inspection owner:

1. Add an owned bounded-stdin process capability or retry-safe private
   temporary-artifact lease; never accept caller paths.
2. Admit an exact `llvm-readobj`/`llvm-objdump` tool bundle generation and bind
   tool bytes/version, argv, limits, and output digests.
3. Decode readobj JSON into bounded section/group/symbol/relocation rows and
   enumerate the complete executable-section closure.
4. Decode objdump raw-byte rows independently and correlate by section,
   address, and bytes; reject unknowns, gaps, overlaps, and drift.
5. Publish an opaque inspection token only after exact retained input,
   complete closure, zero unknown instructions, and cleanup ownership are
   established. Keep it distinct from callable execution evidence.
6. Test tool/input substitution, schema drift, truncation, timeout, nonzero
   exit, relocation outside closure, unknown opcode, duplicate address, output
   caps, cancellation, and retryable reverse-order cleanup.

Implemented policy-independent 6A.2 checkpoint: the bounded normalized
inspection contract now rejects incomplete terminal process facts, malformed
digests/order, resource excess, instruction gaps/unknowns, invalid relocation
targets, and unsupported SIMD claims, and hashes all normalized evidence. Its
focused suite passes 4/4. It deliberately issues no authority; the selected
input/tool owner must construct and retain these facts before publication.

Implemented codec checkpoint: the first pure-Simple readobj JSON codec accepts
only one exact stdin-labeled x86-64 ELF64 relocatable object and rehashes exact
`SectionData` bytes for every executable section. Its focused suite passes 4/4.
Symbol, group, and relocation decoding plus real terminal tool output remain
open; this codec cannot issue authority by itself.

Implemented relocation codec checkpoint: a separate pure-Simple bounded codec
now resolves relocation-section `sh_info` to the patched section and `sh_link`
to the unique symbol table, then validates symbol identity/section and all
section-relative ranges. Its focused suite passes 4/4. Section-group/COMDAT
closure and real tool-owner integration remain open.

Implemented group codec checkpoint: live LLVM output showed duplicate JSON
`Group` keys for multiple COMDATs, so the plan rejects that lossy view. A
bounded pure-Simple codec now decodes exact `SHT_GROUP` bytes plus
`sh_link`/`sh_info`, validates member/signature identity and executable-group
uniqueness, and passes 4/4 focused tests. Actual tool authority remains open.

The target-ID mapping decision is recorded as Option B in
`doc/02_requirements/feature/environment_optimized_dynamic_libraries.md`:
the repository-owned canonical target-triple registry. Its V1/V2 owners exist.
The parser variant planner now canonicalizes registered aliases, checks its
numeric target profile against the selected registry row, and binds the mapping
generation/digest into artifact and cache identities. Full REQ-015 closure still
needs registry-bound profile and receipt identities, plus the backend join's
canonical named-feature-to-word expansion. That join may not compare unrelated
text and numeric digests or infer equality from the v3 preset name.

Implementation lanes:

- Builtin context: add plugin-only immutable target context to
  `BuiltinBackendCompileAdapter`; leave `BackendCompileOptions` unchanged.
- LLVM: pass context into the target configuration and return provider-owned
  effective CPU/features evidence.
- Cranelift: extend the SFFI ISA builder to negotiate and return canonical
  accepted versus rejected features.
- Dynamic: freeze the 16-byte V1 request and add V2 full-request/result codecs
  plus runtime population tests.

Astra review fixes the smallest safe order: implement a separate
`BackendSessionAuthorityOwnerV1` with opaque session/use/result tokens and
retryable close; add a distinct `BackendProviderReceiptV2` and
`BackendCompileResultEnvelopeV2` codec/validator without changing V1 hashes or
its fixed wire; adapt V1 results to `Unknown`; route one builtin object path as
`Unknown`; then add LLVM confirmation from its actual target-machine setup.
The compatibility dynamic lease/session close path now keeps failed private
staging cleanup retryable after unloading the library once; its real-provider
failure/retry spec is added but awaits a source-matched self-hosted runner. This
does not implement the separate session authority or accepted-feature envelope.
Cranelift confirmation follows only after it reports accepted versus ignored
features. Required features must be explicitly accepted under the canonical
registry; sorting/echoing the request is insufficient.

## Levelled single-DSO vector provider (x86-64-v1..v4, NEON/SVE/SVE2, RVV) — 2026-10-24

Scope: the runtime vector provider (`src/runtime/providers/vector/`, ABI
`simple_vector_kernel_abi_v1.h`, admitted by path + SHA-256 in
`src/os/smf/provider_loader.spl`, mapped by `src/os/posix/dynlib.spl`) has a
**levelled** build (`-DSIMPLE_VECTOR_LEVELLED`): one DSO per OS/arch holding
the baseline `bitmap_provider.c`, a baseline dispatcher
(`vector_level_dispatch.c`), and one kernel object per SIMD level
(`vector_level_portable.c` renamed per level, or the existing intrinsic TUs).
The dispatcher probes once, caches the result, and forwards to the highest
level the CPU *and* OS admit, capped by compile-time `SIMPLE_VECTOR_MAX_LEVEL`.
Gate and bench: `scripts/check/check-vector-provider-levels.shs ABS_OUT
[run|qemu|compile|all]` and `src/runtime/test/vector_level_bench.c`. The loader
also accepts `/usr/local/lib/simple/providers/` (FreeBSD/macOS, no `/usr/lib`
under SIP). Legacy single-kernel lanes (`check-vector-bitmap-targets`,
`-http-targets`, `-bitmap-x86-avx512`, `-http-avx512`, `-bitmap-sve`) are
unchanged and still pass. Detail: design § "Levelled single-DSO provider
detail". This is a provider slice under Stage 6; it promotes no parser, JIT
or GPU claim.

### Level table (level 0 = provider refuses with `FEATURE_UNAVAILABLE`)

| Arch | Level | Compile | Runtime admission (all required) | Kernel source |
|---|---|---|---|---|
| x86_64 | L1 | `-march=x86-64` (SSE2) | architectural | `vector_level_portable.c`, auto-vectorized |
| x86_64 | L2 | `-march=x86-64-v2` | SSE3/SSSE3/CMPXCHG16B/SSE4.1/SSE4.2/POPCNT + LAHF-SAHF | same, auto-vectorized |
| x86_64 | L3 | `-march=x86-64-v3` | L2 + FMA/MOVBE/XSAVE/OSXSAVE/AVX/F16C + BMI1/AVX2/BMI2 + LZCNT + XCR0 `0x06` | same, auto-vectorized |
| x86_64 | L4 | intrinsic TUs | L3 + AVX512 F/DQ/CD/BW/VL + XCR0 `0xe6` (macOS: `hw.optional.avx512{f,bw,dq,vl,cd}`) | `bitmap_avx512.c`, `http_avx512.c` |
| aarch64 | L1 | `-march=armv8-a+simd` | `HWCAP_ASIMD` on Linux/FreeBSD; architectural on macOS/Windows/SimpleOS | `*_neon.c` |
| aarch64 | L2 | `-march=armv8-a+sve` (VLA) | + `HWCAP_SVE` | `*_sve.c` |
| aarch64 | L3 | `-march=armv8-a+sve2` (VLA) | + `HWCAP2_SVE2` | `*_sve.c` |
| riscv64 | L1 | `-march=rv64gcv` (VLA) | HWCAP `V` **and** `prctl(PR_RISCV_V_GET_CONTROL)` not OFF | `*_rvv.c` |
| riscv64 | L0 | — | scalar rv64gc is never labelled SIMD: provider refuses | none |
| other | L0 | — | refuses | none |

"Highest admitted" is a *safety* order, not a measured speed order; a lower
level is reached only by honest fallback or an explicit cap, never silently.

### Per-OS probe matrix

| OS \ arch | x86_64 | aarch64 | riscv64 |
|---|---|---|---|
| Windows | CPUID + XGETBV (user-mode legal) | NEON architectural → L1; SVE unprobed (scaffold) | n/a |
| Linux | CPUID + XGETBV | `getauxval(AT_HWCAP=16 / AT_HWCAP2=26)`, declared `extern`, no headers | `getauxval` `V` + `prctl(70)`; current-state OFF → L0 (`riscv_hwprobe` not used) |
| FreeBSD | CPUID + XGETBV | `elf_aux_info(25 / 26)`, no headers | `elf_aux_info(25)` `V` → L1 |
| macOS | CPUID + XGETBV through L3; L4 via `sysctlbyname("hw.optional.avx512*")` because ZMM state is enabled lazily | NEON → L1 | n/a |
| SimpleOS (`__simpleos__`) | CPUID.1:ECX.OSXSAVE before XGETBV, same masks; kernel sets only XCR0 bits it context-switches | L1 NEON (kernel enables FPEN for all userland) | L0 until the kernel exports hwcaps / enables VS |

### Build/test status per cell (2026-10-24)

| Target | Levels | Status |
|---|---|---|
| x86_64-w64-windows-gnu `.dll` | L1–L4 | **run, native** (Xeon W-2135, AVX-512): caps 0–4 parity + timing PASS |
| x86_64-linux-gnu `.so` | L1–L4 | **run, native** (WSL): PASS |
| aarch64-linux-gnu `.so` | L1–L3 | **run, qemu-user**: `-cpu neoverse-n1` → L1, `a64fx` → L2, `max` → L3 PASS |
| riscv64-linux-gnu `.so` | L1 | **run, qemu-user**: `rva23u64` vlen 128 and 256 → L1, `max,v=false` → L0 PASS |
| x86_64/aarch64/riscv64-unknown-freebsd | per arch | compile-only (freestanding, ISA gates) PASS |
| x86_64/arm64-apple-darwin | L1–L4 / L1 | compile-only (ISA gates) PASS; macOS L4 sysctl path not executed here |
| aarch64-w64-windows-gnu | L1 | compile-only PASS |
| x86_64/aarch64/riscv64-unknown-none-elf (`-D__simpleos__`) | scaffold | compile-only PASS; refuses or L1 by construction |
| SimpleOS `.smf` | — | packaging note only |

52 ISA gates across the compile lane pass: baseline objects
(`dispatch-cap4.o`, `provider-cap4.o`) carry no vector-extension
instructions; each `lN` object carries its own level's registers and none
above.

### Measured native kernel ns/op (best of 7, bitmap AND 1 Mbit / HTTP FIND_CRLF 1 MiB)

| Host | L1 | L2 | L3 | L4 | scalar reference |
|---|---|---|---|---|---|
| Windows, Xeon W-2135 | 6114 / 53230 | 5797 / 45592 | 4858 / 35596 | 4334 / 14939 | 12355 / 422540 |
| Linux (WSL), same CPU | 5016 / 50755 | 5114 / 42179 | 4529 / 35901 | 4706 / 25466 | ~12000 / ~323000 |

Scalar reference = the same loops in the bench harness at `-O2` with loop
vectorization disabled, same machine. Bitmap AND is memory-bandwidth-bound
(128 KiB working set), so levels differ by <2x; the byte scan scales with
vector width (L4 is 2.4x L3 on Windows). Under WSL L4 did not beat L3 on
bitmap AND — consistent with AVX-512 license downclock on Skylake-SP; the
selection order is unchanged, the number is recorded.

### Exit criteria

| # | Criterion | State |
|---|---|---|
| 1 | Per-symbol ISA gate: baseline objects vector-free; L1/L2 `xmm` only; L3 `ymm` no `zmm`; L4 `zmm`; aarch64 L1 `v.16b/4s`, L2/L3 `z`-regs; riscv64 `vsetvli` | met (52 gates) |
| 2 | All levels byte-identical to the scalar oracle for every tail length, CRLF across a block edge, max span | met on the run/qemu cells above |
| 3 | Capped variants (`_cap0`..`_cap3`) report `min(cap, host)` and carry distinct implementation IDs and digests | met |
| 4 | Simple-side db (`PureDatabase` RowBitmap AND) and web (HTTP `FIND_CRLF`) probes through the provider on the self-hosted chain, receipt names the executed level | **open** — not in this evidence set |
| 5 | Below-max reason codes (`cpu-missing:` / `xcr0:` / `cap:` / `os:`) in receipts | **open follow-up** — only `selected_level` exists |
| 6 | `.init_array` / `DT_INIT` / PE TLS-directory emptiness checked by the gate (today it holds by construction only) | **open follow-up** |
| 7 | Legacy lanes green; unknown arch refuses | met |

### Risks found and mitigations

| Risk | Mitigation (state) |
|---|---|
| Headline-bit admission (old `available()` = AVX512F only) while clang emits BMI2/LZCNT/MOVBE (v3) or BW/DQ/VL/CD (v4) | full per-level feature conjunction in `probe_level()` (done) |
| CPUID advertises AVX-512 but OS/hypervisor masks XCR0 | XCR0 `0x06` for L3, `0xe6` for L4, after OSXSAVE (done) |
| macOS Intel enables ZMM state lazily, XCR0 would deny | `hw.optional.avx512*` sysctls for L4 (done, untested here) |
| `xgetbv` `#UD` when OSXSAVE is clear (SimpleOS, thin hypervisors) | OSXSAVE is part of the v3 conjunction tested first (done) |
| RVV: HWCAP `V` set but per-process vector OFF | `prctl(PR_RISCV_V_GET_CONTROL)` current-state check (done) |
| Hybrid cores / per-thread SVE VL / RVV VLEN | trust OS-normalised CPUID/hwcaps; SVE/RVV kernels are VLA; qemu vlen 128 and 256 both PASS (done) |
| v4 code loaded on a v1 CPU | no constructors/static init/TLS in level TUs; only the dispatcher references `lN` symbols; ISA gate (done); init-section emptiness gate (open) |
| LTO / `always_inline` pulling wide code into the baseline TU | no LTO in the build; ISA gate on the baseline objects (done) |
| Probe on every call | one probe, `atomic_int` cache (done) |
| One digest for all levels hides the executed level | `simple_vector_selected_level_v1()` (done); reason codes (open) |
| Capped build admitted under the production name | cap folded into implementation ID and `_capN` file name (done) |
| Non-deterministic PE digest | `-Wl,--no-insert-timestamp`, lld, explicit `.def` exports (done) |
| AVX-512 downclock makes L4 slower on short/bandwidth-bound spans | measured and recorded; selection stays safety-ordered; cap is the only override |
| Linux-only `<asm/hwcap.h>` on FreeBSD | numeric aux keys, no headers (done) |
