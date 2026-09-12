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
| Generated JIT/AOT/binary SIMD | Target-codegen contracts and a parser variant build plan separate host and target. Existing AOT is whole-module; parser sibling emission, target-aware JIT materialization, cache V2 implementation, and emitted/executed ISA proof are missing. | Design/contracts in progress | Cache V2 validation, actual sibling artifacts/JIT units, disassembly/metadata checks, callable execution, rollback |

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

Implemented checkpoint: the strict loader-to-owner path and real builtin LLVM
object producer now issue V2 `Unknown` evidence with exact byte lifetime. This
does not satisfy 6A.1c confirmation; the next gate is backend-authored LLVM
accepted-feature output from target-machine configuration.

6A.1c begins with propagation, not receipt issuance: carry normalized request
CPU/features through builtin adapter construction into LLVM/LLVM-lib target
configuration, reject unsupported features before emission, and return the
effective configuration alongside the exact bytes. Only then may the result
owner convert Unknown to AcceptedExact.

Implemented checkpoint: builtin LLVM now compiles through its retained exact
plugin target context and returns effective CPU/features with exact bytes. The
session authority issues AcceptedExact only when those canonical features equal
the request. This completes LLVM configuration acceptance, not instruction
inspection or execution. Cranelift and dynamic V1 remain Unknown.

Implemented inspection checkpoint: a bounded strict x86-64 ELF64 ET_REL
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

User decision gate: select the target-ID mapping policy in
`doc/02_requirements/feature/environment_optimized_dynamic_libraries_options.md`.
The parser backend join must bind the chosen registry version/digest and a
canonical named-feature-to-word expansion; it may not compare unrelated text
and numeric digests or infer equality from the v3 preset name.

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
Cranelift confirmation follows only after it reports accepted versus ignored
features. Required features must be explicitly accepted under the canonical
registry; sorting/echoing the request is insufficient.
