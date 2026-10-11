> Integration status, 2026-10-11: user-selected variation direction for Item 5; implementation and target qualification remain incomplete. This imported proposal is retained as supplied (SHA-256 `6e470a5c531aae39d6adec12c129986395681f5d3591bd4380db1113b232d3e1`). Its a9777ac evidence baseline is historical. The [current shared-interface reconciliation](perf/item5_shared_provider_interfaces_2026-10-09.md#2026-10-11-variation-and-sosix-integration) records corrections against release 02b150b385013d21bc408b45244431de85d391de. Execute its P0–P9 migration through the existing Item 5 plan; do not create a parallel plan or reinterpret P5 as Item 5 Phase 5.
# Simple: Isolated SIMD, GPU and Platform Variations with SOSIX Consolidation

**Final integrated design and migration plan — 2026-10-10**  
**Suggested repository destination:** `doc/05_design/compiler/simd_gpu_sosix_variation_final_2026-10-10.md`  
**Supersedes:** `simple_simd_gpu_target_variations_2026-10-10.md` from this conversation.  
**Scope:** CPU architecture; x86 SIMD including AVX-512; Arm NEON/SVE/SVE2; RISC-V RVV; Qualcomm accelerator separation; CUDA/Metal/Vulkan; 32/64-bit, ABI and OS variation; SOSIX host-service consolidation; compiler/runtime/provider ownership.  
**Status:** Final proposal, not an implementation-completion claim. No repository files were changed and no compiler, QEMU, GPU or performance tests were executed for this document. Illustrative schemas and new names below require implementation unless explicitly marked existing.

**Evidence baseline:** repository snapshot `a9777ac75fa5d64c6741de8981a9d13815990179`; current-turn reads of SOSIX and environment-variant sources, plus the preceding source audit and its attached report. Dated repository reports retain their original observation dates; a source/spec file is not proof that a native execution path passed. Reference IDs link to pinned repository files or primary external documentation in §18.

## Contents

0. [Binding decisions](#0-binding-decisions)
1. [Current implementation and corrections to the previous report](#1-current-implementation-and-corrections-to-the-previous-report)
2. [Isolation and single-owner rules](#2-isolation-and-single-owner-rules)
3. [Target, capability and binding ownership](#3-target-capability-and-binding-ownership)
4. [Directory layout and sparse variation resolution](#4-directory-layout-and-sparse-variation-resolution)
5. [SIMD and accelerator feature families](#5-simd-and-accelerator-feature-families)
6. [ABI, 32/64-bit and OS separation](#6-abi-3264-bit-and-os-separation)
7. [Shared vectorization and GPU planning](#7-shared-vectorization-and-gpu-planning)
8. [Options, tags and enforceable evidence](#8-options-tags-and-enforceable-evidence)
9. [SOSIX consolidation contract](#9-sosix-consolidation-contract)
10. [GPU execution through SOSIX without duplicate runtimes](#10-gpu-execution-through-sosix-without-duplicate-runtimes)
11. [Build, cache, bootstrap and hot-path performance](#11-build-cache-bootstrap-and-hot-path-performance)
12. [Enforcing isolation and preventing duplication](#12-enforcing-isolation-and-preventing-duplication)
13. [Nonbreaking implementation and retirement plan](#13-nonbreaking-implementation-and-retirement-plan)
14. [Verification matrix](#14-verification-matrix)
15. [Worked composition examples](#15-worked-composition-examples)
16. [Documentation, Spipe and traceability](#16-documentation-spipe-and-traceability)
17. [Completion criteria](#17-completion-criteria)
18. [Sources](#18-sources)

## 0. Binding decisions

**Isolate implementation differences, not the entire system. Share each algorithm, contract, lifecycle and selection rule under one authoritative owner; place only irreducible ISA, ABI, OS or device differences behind narrow provider interfaces.** A new target must not require a copied compiler, standard library, SOSIX implementation, Future, parser, scheduler or loader.

| Decision | Final rule |
|---|---|
| Variation discovery | Retain the existing resolver-only `variants/` root and `config/var.sdn`. Do not create `var/` or a competing target-directory resolver. |
| Source placement | `variants/` contains sparse module overlays and selection metadata. Concrete instruction encoders and host/device providers remain isolated inside their existing layer-owned implementation directories. A central index is not a reason to move or duplicate their source. |
| Target and binding types | Reuse `EnvironmentSnapshotV1`, `VariantDescriptorV1`, `BindingPlanV1`, `TargetCodegenProfileV1`, the feature registry, catalog, admission and binding runtime already present in `composition/environment_variants/`. Do not introduce peer implementations named `TargetProfile`, `CapabilitySnapshot` or `VariantResolver`. |
| Canonical semantics | One language/MIR meaning, one numerical contract, one operation-family specification and one shared legality analysis. Different lowering strategies are permitted only when they preserve that contract or explicitly request a different one. |
| CPU vectorization | Keep fixed/scalable SIMD lowering distinct from GPU SIMT. Use the existing MIR vectorizer; add target adapters and qualified transformations rather than one vectorizer per ISA. |
| GPU compilation | Reuse the existing ProcessingIR/portable-compute direction and GPU emitters. Share kernel semantics and planning; keep PTX, SPIR-V and MSL emission separate. |
| SOSIX | Consolidate OS-service access, capabilities, operation completion and resource retirement under existing SOSIX/SimpleRing contracts. Do not make SOSIX own arithmetic, compiler IR, scene/layout or algorithm selection. |
| Async/sync/GC | Async is the default for potentially blocking service operations. Sync APIs adapt the same operation; exact native aliases remain possible where all semantics match. GC/no-GC and sync/async families must not copy algorithm bodies. |
| Runtime cost | No new ring submission for a scalar/SIMD arithmetic call. No provider discovery, CPUID, string-based selection or filesystem probing inside an inner loop. No extra queue layer merely to make names uniform. |
| Migration | Move an owner or redirect its callers; never copy it into a new “common” directory and leave both implementations live. Compatibility facades are bounded, behavior-free and explicitly retired. |

These decisions tighten the earlier report in three important ways. First, existing environment-variant machinery replaces its proposed new ownership layer. Second, generic pointer-width changes are data-layout parameters, not a reason to populate `bits32/` and `bits64/` copies. Third, GPU runtime integration uses the SOSIX consolidation plan rather than a second “unified compute runtime.” [R01][R02][R03][R04]

**What “no duplication” permits:** target-generated machine code, genuinely different ISA kernels, distinct OS API adapters and an independent test oracle. It does not permit copied control flow, parallel error tables, separately maintained equivalent registries, or an entire backend family duplicated because only its calling ABI differs.

## 1. Current implementation and corrections to the previous report

### 1.1 Existing owners that must be reused

| Area | Current evidence | Final treatment |
|---|---|---|
| Environment snapshot and provider descriptors | `src/lib/nogc_sync_mut/composition/environment_variants/contracts_v1.spl` already defines fixed-width, arena-referenced snapshots, device records, descriptors, bindings and plans; descriptors include OS, ABI, format, endian, pointer width, CPU/device requirements, effect and numerical constraints. | Extend these records through a negotiated schema; do not define equivalent records in compiler, runtime and SOSIX separately. [R01] |
| Catalog and runtime binding | The same package exports `catalog_v1`, `admission`, `policy`, `dependency_resolver_v1`, `binding_runtime_v1`, artifact admission and receipts. | Connect existing consumers to this owner. A catalog or receipt type being present does not establish that every production route uses it. [R02] |
| Host/target separation | `target_codegen_profile_v1.spl` distinguishes requested features, backend acceptance, artifact declarations, emission, selection and execution evidence. | Use these stages for SIMD/GPU reporting. Preserve the difference between “can emit” and “may run here.” [R03] |
| Registered architecture subset | The inspected environment-contract and target-codegen validators accept x86_64, AArch64, RV64 and wasm32. The canonical driver target registry has a similarly limited initial set. | ARM32, x86-32, RV32 and additional OS/ABI combinations need registered identities and validator/codec parity—not just new directory names. [R01][R03][R17] |
| SOSIX contract library | Common operation, completion, error, capability, wait and service-ID contracts already exist. `src/os/sosix/core/*` is intended as the compatibility surface over these common owners. | Keep shared semantics in the library; SimpleOS remains a provider of the same contracts. [R04][R05][R06] |
| Hosted SOSIX | `SosixHostedFs` composes a SimpleRing and operation retirement state. The documented portable driver performs synchronous host I/O while servicing submissions. | Distinguish a ring-shaped API from native asynchronous completion. Qualify each real provider separately. [R05][R06] |
| SIMD frontend and vectorizer | Existing `simd_capabilities`, `feature_caps*`, `auto_vectorize*`, alias checking, receipts, and native encoders were inspected in the preceding audit. `AutoVectorize` is marked Active for a narrow, guarded static-loop subset. | Preserve that path; generalize its target context and lowerings incrementally. Do not re-enable previously unsafe dynamic/tail rewrites by changing a status flag. [R18][R19][R20][R21] |
| GPU compilation | Portable compute emission supports CUDA/HIP/OpenCL/Metal/WebGPU in one enum, while Vulkan/SPIR-V is also represented through a separate route. | Reconcile enum/descriptor coverage and shared planning, not replace both with a third backend framework. [R23][R24][R25] |
| Module overlays | `variants/__init__.spl`, `config/var.sdn` and `module_resolver/var_resolution.spl` implement the current overlay model. Rust stdlib SIMD-root lookup is an additional historical path. | One normalized source-resolution decision with a legacy-input adapter; no independent precedence or cache policy for old SIMD roots. [R13][R14][R15][R16] |

### 1.2 SOSIX status must not be overstated

The repository's 2026-09-26 review and 2026-09-28 addendum are especially important. They describe incomplete route census and retirement proof, distributed compiler/interpreter/loader host effects, incomplete production loader binding, and unqualified GPU/SimpleOS live routes. They also correct an earlier Promise defect: the later source publishes a result through the paired Future, while task wake, lifetime/retirement and cross-runtime qualification remain open. **Do not repeat the old claim that current `Promise.complete` never publishes; do not promote source-level pairing into proven full async semantics either.** [R05]

The SOSIX guide contains dated and conflicting availability sections. It records Windows/macOS native backend source that was not integrated into runtime source lists at its observation date, and an older “not available” list beside newer raw-descriptor progress. Treat it as historical evidence, not a complete current platform-support matrix. Re-establish live build/link/behavior evidence before moving any row to supported. [R06]

The same current-state review reports that referenced historical performance-baseline files were absent at its baseline. Therefore this design deliberately does **not** adopt a numeric SOSIX overhead or speedup from those old links. Capture a reproducible baseline in the implementation lane. [R05]

### 1.3 Corrections to the previous architecture

| Earlier direction | Final correction |
|---|---|
| “Create `TargetProfile` / `CapabilitySnapshot` / selection owners.” | Those are conceptual roles already substantially represented by environment-variant contracts. Extend the existing owner; names in this document are views, not new peer schemas. |
| “One immutable snapshot for a session.” | Keep immutable snapshots, but distinguish build target, process, worker/thread vector state and device generations. SVE length and other execution permissions cannot safely be treated as permanently process-global. [E03][E04][E05] |
| “Put SIMD or bitness logic into overlay groups.” | Use overlays only for actual module replacement. ISA instruction selection and ordinary pointer-width layout stay in target lowering; most bitness variation requires no duplicate source. |
| “A common compute scheduler.” | Share compiler planning and existing task/executor integration. Do not add another runtime scheduler, Future or queue envelope for GPUs. |
| “SOSIX-style async submission.” | Bind to the actual SOSIX operation, SimpleRing token and payload-lease lifecycle. Similar-looking private types do not count as integration. |
| “A CPU fallback always exists.” | A fallback must be explicit and semantically valid. `require` constraints, device-only resources and partially executed effectful operations may require an error instead of CPU fallback. |
| “Vector width proves ISA.” | It does not. NEON, AVX2, AVX-512 EVEX and scalable-vector requirements need exact lowering evidence; 256 bits is not synonymous with AVX2. |

## 2. Isolation and single-owner rules

### 2.1 Orthogonal variation axes

| Axis | What it may change | What it must not change |
|---|---|---|
| CPU family / ISA | Machine instructions, legal operations, register constraints, scheduling cost | Portable algorithm semantics, host filesystem behavior |
| Vector form | Fixed/scalable lanes, masks, tail scheduling, register grouping | Calling ABI by implication; ordered numerical results without authorization |
| Microarchitecture tuning | Cost parameters, unroll/tile preferences, cache hints | Feature legality or API contract |
| ABI / data layout | Argument passing, stack, aggregate layout, relocation/unwind interfaces | Numerical algorithm or OS-service lifecycle |
| Pointer width / endian | Checked address arithmetic, scalar legalization, boundary encoding | Entire collection/parser/runtime implementations |
| OS / execution environment | Native services, wait mechanism, device access, dynamic loading and permissions | A different SOSIX result or Future model |
| GPU API / device | Kernel artifact, resource binding, command encoding, API synchronization | Copies of every portable algorithm or another host runtime |
| Memory / concurrency profile | Allocation permission, bounded capacity, executor policy | Copied sync/async/GC versions of semantic bodies |
| Placement | Static, dynlib, SMF, JIT, contained worker | Different computation results or bypassed admission |

The product of these axes is a **configuration**, not a directory tree and not a set of manually maintained codebases.

### 2.2 Single ownership by responsibility

| Responsibility | Authoritative home / reuse point | Consumers |
|---|---|---|
| Language and operation meaning | Existing frontend, type system, MIR and operation-family specifications | Interpreter, all native and GPU backends |
| Feature identities and target admission | Existing `composition/environment_variants` contracts, feature registry, catalog and admission | Compiler adapter, source resolver, runtime loader, device-session composition |
| Target names and profiles | Existing canonical target registry plus preset-to-registry translation | CLI, build runner, codegen |
| ISA legality/cost/lowering | Existing `feature_caps*` seam and layer-owned backend modules | Shared vectorizer and instruction selector |
| Host-service operation semantics | `std.common.contracts.sosix` | Hosted SOSIX and SimpleOS |
| Ring/task protocol | `std.common.contracts.execution.simple_ring_async_v1` | SOSIX, host executor, GPU proxy adapters and qualified native transports |
| Future/Promise result and wake contract | Canonical async owner and existing task compatibility bridge | GC/no-GC and sync/async facades |
| Native service implementation | Qualified provider below SOSIX | Same service regardless of app or compiler caller |
| GPU algorithm planning | Existing portable-compute / ProcessingIR / MIR optimization owners | CUDA, Vulkan, Metal and other emitters |
| GPU native execution | Existing backend runtime provider bound into SOSIX resource lifecycle | Prepared device sessions, rendering, compute, compiler offload |
| Dynamic loading policy | Existing loader and environment admission/binding owners | Compiler plugins, runtimes, GPU libraries |
| OS loading and executable mappings | SOSIX memory/library service implementation | Loader policy above it |

A new abstraction is allowed only for a responsibility that has no owner, and only after the ownership map identifies why an existing owner cannot be extended. A new public facade alone is not an additional implementation owner.

### 2.3 Allowed and forbidden dependencies

**Common semantic code** may depend on pure contracts, stable abstract operation descriptions and explicit inputs. It may not detect the host OS, inspect CPUID, open a library, call `rt_*`, enumerate devices, or import CUDA/Metal/Vulkan implementation modules.

**The shared vectorizer** receives `TargetCodegenProfileV1` and admitted target-lowering capabilities. It may ask a resolved target-cost interface; it may not choose a machine by checking the build host or importing an OS-specific runtime.

**A concrete provider** may depend on common contracts and a small shared native helper layer. It must not import another provider's private implementation as a shortcut. Shared code between two providers is moved to an explicitly owned helper, not accessed through one provider's directory.

**Composition roots** are the only places that bind implementations to contract slots. Their decisions are recorded in `BindingPlanV1`; ordinary app/library code does not contain `if windows / if avx512 / if cuda` dispatch ladders.

**Artifact isolation** uses private/internal implementation symbols and an explicit versioned facet entry table. Distinct multiversion bodies may have distinct generated symbols, but public semantic entrypoints and state owners remain unique. Prevent accidental symbol interposition between plugins; bind and retain the exact artifact/provider generation. Source-module isolation is not a security sandbox: untrusted native code requires an admitted contained-worker or equivalent isolation mechanism, not merely placement under `variants/`.

**Kernel/freestanding code** may bind common contracts directly to SimpleOS providers. It must not import the hosted SOSIX composition merely to obtain a type; no implicit libc, host thread pool or GPU SDK may enter that closure. [R04]

### 2.4 The rule for an actual algorithm difference

A scalar reference, a vectorized loop and a tiled GPU kernel can be legitimate implementations of the same operation. Keep one operation specification and, where feasible, one portable body or recipe that the compiler lowers differently. A hand-tuned provider must declare its semantic identity, numerical mode, required features, test oracle and reason that generation was insufficient. Copying its shape checks, error mapping, transfer policy or fallback ladder is still forbidden.

A mechanically generated native stub or code variant is not a second human-maintained source. It must record its generator and source digest, be reproducibly regenerated, and be excluded from manual edits. An independent oracle in tests is also legitimate; requiring production and oracle to share the same bug-prone body would weaken validation.

## 3. Target, capability and binding ownership

### 3.1 Reuse the existing pipeline

```text
registered output target + compile policy ──> TargetCodegenProfileV1
                                                   │
                                   backend acceptance / emission
                                                   │
                                             target artifact

host / worker / device probes ──> EnvironmentSnapshotV1
                                             │
VariantDescriptorV1 catalog + policy + dependency lock
                                             │
                       existing eligibility / admission / catalog selection
                                             │
                                        BindingPlanV1
                                             │
                    existing loader + binding-runtime publication / session
                                             │
                          direct callable / prepared provider table
```

These records already exist. The work is production wiring, missing target rows and schema extensions—not recreating the diagram as a parallel package. [R01][R02][R03]

The canonical registry currently lives in the driver. Runtime consumers must not import the compiler driver to resolve a number. Generate or expose a minimal immutable registry projection under the existing common contract authority; move pure ownership only when necessary, leaving one facade at the original path. Do not maintain a second independently edited runtime registry.

### 3.2 Distinct facts with explicit provenance

Use different views of the existing records for the following roles:

- **Output target:** declared ISA, ABI, object format, endian and layout; controls code generation, including cross-compilation.
- **Execution process:** detected architecture, hardware feature set, OS-authorized state, loader permissions and policy.
- **Worker/thread execution domain:** CPU affinity/feature compatibility, current vector mode/length where relevant and established context-state contract.
- **Accelerator session:** device identity, API/driver, enabled features, memory domain and resource generation.
- **Implementation:** emitted/packaged features, contract version, semantic identity and resource bounds.

Never synthesize runtime evidence from a target flag. A user can request an AVX-512 deployment artifact on a non-AVX-512 machine; that does not allow the compiler process or test runner to execute it.

For CPU execution:

```text
eligible = target/ABI/layout compatible
        && artifact admitted
        && required_cpu ⊆ hardware_features
        && required_os_state ⊆ OS-authorized state
        && required_cpu ⊆ policy_allowed_features
        && executor domain satisfies vector-state assumptions
        && contract/semantics/resource constraints satisfied
```

GPU admission additionally checks the bound API/device, enabled features, kernel argument layout, memory visibility, queue capabilities and compiled artifact compatibility. Selection preference and measured performance are applied **after** eligibility, not instead of it.

### 3.3 Feature model and registry extension

Keep existing IDs stable; allocate new architecture and feature IDs through the same registry owner. Extend x86 subfeature dependencies, ARM32/MVE, RV32/Zve and device features through reviewed rows. Persist SDN names for people and numeric/bitset representations for compiled interfaces. Unsupported or unknown required capabilities fail closed.

The current v1 schema has fixed-width fields and caller-owned arena references. Preserve those ABI properties. A new incompatible record layout needs version negotiation, converter fixtures and old-reader rejection. A minor-version additive field is allowed only where an existing extension mechanism specifies its absence semantics; do not quietly append bytes to a frozen struct and assume all plugins understand them. [R01]

Separate **hardware ability**, **OS authorization**, **implementation availability**, **policy permission** and **evidence of execution**. A coarse SIMD tier is a display/package convenience. It cannot replace instruction-specific feature requirements.

### 3.4 Probe authority and dynamic state

Architecture probes and OS-state probes have different owners, but they produce one admitted snapshot. CPUID decoding is x86-specific; Linux auxiliary vectors, Windows facilities and Darwin queries are OS-specific adapters. Extract shared decoding tables rather than duplicating the full probe in every runtime family.

Linux documents SVE vector length as thread state and RVV enablement controls through its vector interface. Accordingly, a process-global snapshot is not sufficient evidence for every task running on every worker. Use vector-length-agnostic code where possible. Fixed-VL specializations require a compatible worker domain; do not leave scalable vector values live across a migration or mode-changing boundary without a defined preservation rule. [E03][E04]

For heterogeneous CPU sets, use the guaranteed common executable feature set or bind work to a qualified affinity domain. A task migration must not enter a weaker domain while executing a stronger ISA variant. Revalidate at controlled domain/worker transitions rather than repeating probes per operation.

Refresh snapshots on policy reload, device reset/replacement or relevant domain changes. Publish a new generation atomically and keep old sessions alive until drained. Do not mutate a snapshot that existing optimized code or cache entries already reference.

### 3.5 Registry and binding are not a universal hot-path dispatcher

The source resolver chooses module files; the compiler chooses lowering; the runtime chooses a callable/provider. These are different **consumers of one metadata and policy authority**, not the same loop or the same cache. Reuse semantic compatibility, identity and feature rules; retain specialized fast paths appropriate to each consumer.

A published binding may resolve to a direct call, a statically specialized trait, a function pointer or a prepared GPU session. There is no requirement to call the catalog on each invocation. Artifact authentication/admission belongs before executing provider initialization or code, with retained evidence—not inside each arithmetic or FFI call.

## 4. Directory layout and sparse variation resolution

### 4.1 One discovery location, layer-owned implementation locations

Keep `variants/` for source overlays and a discoverable view of the existing provider catalog. Do **not** use it as a dumping ground for copied native/runtime/OS trees. Existing compiler directories, native providers and SimpleOS paths remain their physical owners until a move has an independently justified benefit.

```text
variants/                                  # EXISTING: resolver-only source overlays
  __init__.spl                             # EXISTING: bootstrap-safe SDN manifest
  FILE.md                                  # EXISTING: root contract
  platform/...                             # EXISTING OS selection seams
  hw/...                                   # existing group; source only where needed
  lib/crypto/...                           # EXISTING semantic slot selection
  ui/renderer/...                          # EXISTING renderer-selection seams
  index.sdn                                # PROPOSED generated view of existing catalog
  # Optional new group directories appear ONLY for a real source seam.
  # No full bits32/, bits64/, gc/, async/ copies of common code.

src/lib/common/
  contracts/execution/simple_ring_async_v1.spl   # EXISTING task/ring authority
  contracts/sosix/*_v1.spl                       # EXISTING SOSIX semantics
  ...                                           # portable algorithm owners

src/lib/nogc_sync_mut/composition/environment_variants/
  contracts_v1.spl  feature_registry_v1.spl       # EXISTING
  target_codegen_profile_v1.spl  catalog_v1.spl
  admission.spl  policy.spl  binding_runtime_v1.spl
  # source of provider identity/admission/binding, not a parallel new registry

src/lib/nogc_async_mut/
  async/                                  # canonical Future/Promise facade
  async_ring/                             # existing hosted ring/executor integration
  sosix/                                  # existing host-service composition/facades

src/compiler/
  00.common/  10.frontend/  20.hir/  50.mir/       # shared semantics
  60.mir_opt/                                    # common analysis/rewrites
  70.backend/
    feature_caps*.spl                           # existing target-cost facade
    backend/native/                             # existing ISA encoders
    backend/gpu_portable_compute.spl            # existing shared GPU emitter seam
    # optional subdirectories by ISA/ABI only when moving the actual owner
  80.driver/                                    # target registry producer / binding
  99.loader/                                    # loader policy + source resolver

src/runtime/
  providers/vector/                       # existing irreducible ISA kernels
  platform/                               # existing native OS shims/providers
  # shared backend implementations remain under their actual audited owner

src/os/
  sosix/                                  # SimpleOS provider + compatibility exports
  kernel/                                 # privileged HAL, interrupts, native queues

config/var.sdn                            # EXISTING profile input
build/...                                # generated tables, binaries, caches, receipts
var/...                                  # runtime state, NOT source variations
```

`variants/index.sdn` is a **generated navigation view**, not a second catalog or hand-maintained registration source. Prefer generating it from existing descriptors and resolver metadata. It may show `slot -> owner source -> target predicates -> artifact -> evidence` without taking ownership of any of those facts.

### 4.2 Sparse slots instead of unrestricted overlay replacement

The current resolver orders selected roots before defaults. That compatibility behavior should remain while migrating known seams. New/core seams need stricter rules: each overridable module or facet declares its semantic contract and allowed owning group. A renderer group cannot override an arbitrary file API; a SIMD group cannot replace Future semantics. [R13][R15]

**Proposed slot metadata, not current accepted syntax:**

```sdn
slots:
  bitmap.and:
    semantic_owner: bitmap_operation_contract
    implementation_owner: existing_vector_provider_owner
    varies_by: [cpu.isa, cpu.tuning]
    must_not_vary_by: [os, pointer_bits, gc, async]
    fallback: scalar_reference
    public_boundary: existing_buffer_contract
  sosix.file.positioned:
    semantic_owner: std.common.contracts.sosix.file_operation_v1
    varies_by: [os, service_provider]
    must_not_vary_by: [cpu.simd, gpu.api, gc]
    fallback: portable_provider_when_policy_allows
```

The names are labels to map onto current descriptor identities, not a parallel type or service-ID system. Ordinary source keeps stable imports. Direct `use variants.*` and `use var.*` remain disallowed.

### 4.3 Resolution algorithm

At a session boundary, normalize config, target, slot ownership and available descriptors once. Compile supported applicability predicates into a bounded form: exact IDs, sets, intervals and feature masks. Reject arbitrary executable predicates in bootstrap manifests.

For each needed slot:

1. Collect only candidates registered for its owner/contract.
2. Filter against the correct context: output target for source/codegen, execution environment for loaded callables, bound device for GPU work.
3. Check ABI, effects, numerical policy, resource limits, artifact admission and dependencies.
4. Apply explicit policy and cost to eligible candidates.
5. Resolve exactly one binding per single-provider slot, or an explicitly declared ordered set for a multiversion slot.
6. Reject unresolved ties unless a documented priority rule selects one; never guess from directory traversal order.
7. Record fallback or rejection and include the selected source/artifact identity in the appropriate cache key.

A composite need is modeled by dependencies between slots. For example, a Vulkan runtime depends on an OS dynamic-library service and an OS surface adapter. It does not require a copy named `vulkan_windows_arm64_nogc_async`. When a genuinely joint ABI/OS constraint exists, register one narrow adapter with both predicates; do not create a global product-of-axes precedence hierarchy.

### 4.4 No generic bitness overlays

`pointer_bits`, integer ABI, endian and alignment are target data. Use shared layout algorithms and parameterized legalization; generate width-specific code. Add a width-specific module only when a different primitive is actually required, such as a proven 64-bit atomic emulation on a 32-bit target. Place that primitive under the atomics provider owner and record its blocking/interrupt constraints.

A 32-bit target cannot fall back to a 64-bit ABI artifact. A scalar fallback may remove SIMD requirements, but it cannot erase OS, object format, endian, resource-layout or pointer-width incompatibility.

### 4.5 Legacy bridge and removal

Map old `platform`, `hw`, SIMD tier names and older stdlib variant roots into the same normalized selection. Preserve existing CLI spellings with deprecation diagnostics only where required. Maintain one candidate decision; do not probe the legacy resolver again after a failed new result.

During migration, an old source path may be a re-export of the relocated owner. A wrapper is allowed only when the current language cannot express the alias; it must contain no algorithm or policy and must have its call/ABI cost checked. A compiled session must not contain both the legacy implementation and the new implementation as competing definitions of the same slot.

## 5. SIMD and accelerator feature families

Feature support is **a set of independent capabilities**, not one ordered enum. Width alone does not establish whether an instruction is legal. CPU family and OS-state constraints also apply.

### 5.1 x86/x86-64

| ISA/extension | Vector width | Important capability | Targeting rules |
|---|---:|---|---|
| Scalar/x87/SSE legacy | Scalar and 128-bit | Scalar math, older FP | x86-32 baseline depends on selected target; don't assume SSE2 on every IA-32 CPU. |
| SSE2 | 128 | Integer and FP vectors | Baseline for ordinary x86-64 psABI targets. |
| SSE3, SSSE3, SSE4.1, SSE4.2 | 128 | Additional horizontal, shuffle, text/CRC, integer ops | Check each subextension independently. SSE4.2 is **not** shorthand for AVX. |
| AVX | 128/256 | VEX-encoded FP SIMD | Requires OSXSAVE + appropriate XCR0 XMM/YMM state on the executing OS. |
| AVX2 | 128/256 | 256-bit integer arithmetic, gather, richer SIMD | Requires AVX usability and AVX2 CPUID. FMA/F16C/BMI are separate features. |
| AVX-512F | Primarily 512; shorter forms require their specified extensions | Foundation instructions, opmask, EVEX | Requires full OS-managed opmask/ZMM state for AVX-512 use; use op-specific subfeature checks. |
| AVX-512CD/DQ/BW/VL | Subsets of 128/256/512 | Conflict detection; integer; byte/word; shorter EVEX vectors | `x86-64-v4` represents a defined baseline subset; not every AVX-512 extension. |
| AVX-512 VBMI/VBMI2/IFMA/VNNI/BF16/FP16/VPOPCNTDQ/… | Depends on subset | Permute, crypto-related integer, dot-product, low-precision arithmetic | Independent dispatch predicates, no inferred blanket AVX-512 availability. |
| AVX10 (future-capable profile) | Width reported by ISA/version | Newer unified AVX extension enumeration | Model the explicitly supported ISA version and vector-width capabilities; do not infer executable instructions from an unversioned AVX10 label. Qualify new versions separately. |
| AMX | Tile state rather than regular vector registers | Matrix/tile operations | Separate matrix capability and OS tile-state permission; not an AVX-512 width. |

**Profiles:** `x86-64-v2`, `-v3`, `-v4` are standardized cumulative microarchitecture baselines; they are useful distribution-package labels, not a substitute for the feature bitset. Add custom `avx512_core_256`, `avx512_core_512`, `avx512_vnni` or `avx10_256`-style **internal recipes** only when backed by exact feature predicates. Runtime selection should allow AVX2 to win on hardware where AVX-512 lowers clock rate or has higher transition cost.

### 5.2 Arm (including Qualcomm ARM CPUs)

| ISA/accelerator | Width model | Architecture | Plan |
|---|---|---|---|
| ARMv7 NEON / AArch64 Advanced SIMD (NEON) | Fixed 64/128; typical vector operations 128-bit | ARM CPU, including Qualcomm Oryon and Apple Silicon | Primary ARM CPU SIMD provider; distinguish ARM32 optional NEON from the selected AArch64 execution/OS contract. |
| ARMv8-A optional scalar/NEON extensions | Fixed | Dot product, FP16, BF16, crypto, I8MM, etc. | Feature-specific selection; never deduce from a vendor name. |
| SVE | **Scalable** 128–2048-bit architectural range | Optional AArch64 CPU feature | Runtime `VL`, predicates, loop strip-mining; do not set VL once at build time. |
| SVE2 | Scalable | Extends SVE for richer integer/DSP/media processing | Separate feature ID, valid VLA lowering; not universally present on ARMv9 devices. |
| SME/SME2 | Scalable vectors **and matrix tiles** | Optional Arm feature | Separate matrix plan, streaming mode, OS context/ABI restrictions; later phase. |
| MVE/Helium | 128-bit fixed/predicated | Some ARM M-profile microcontrollers | Distinct ARM32 profile, not AArch64 NEON. |
| Qualcomm Hexagon HVX | Usually 128-byte vector on documented generations | **Separate Hexagon DSP/NPU processing domain** | Make an optional `hexagon_hvx` accelerator backend, not an `aarch64` CPU SIMD subfeature. |
| Qualcomm Adreno | GPU subgroup/thread model | Vulkan/OpenCL/other exposed GPU APIs | Use GPU device capability and driver support; not a CPU ISA. |

**Qualcomm decision:** Snapdragon ARM cores use the ARM feature probe; Hexagon HVX/HTP and Adreno are separately enumerated devices. This avoids falsely adding `has_hvx` to the ARM CPU executable capability mask. Treat vendor/model names as tuning hints, never executable-feature proof. The preceding audit found an explicit Apple-M SVE/SVE2 guard in the current detector; retain the safe behavior until a target-specific feature and OS-state contract justifies a change.

### 5.3 RISC-V

| Extension | Width model | Plan |
|---|---|---|
| RV32/RV64 scalar base and optional F/D | 32/64-bit GPR and available FP | Target ABI ILP32/LP64 and F/D extensions separately. `RV64` does not imply RVV or FP. |
| RVV 1.0 / `V` | **Scalable** VLEN/ELEN and SEW/LMUL | Emit `vsetvli`/`vsetvl`, tail and mask policy; VL is selected dynamically per vector operation/strip-mining iteration. |
| Embedded vector profiles (`Zve*`) | Profile-dependent integer/FP element support | Support reduced RVV profiles without assuming the full `V` extension. |
| `Zvfh`, BF16 variants, vector crypto `Zvk*` | Extension-dependent | Independent feature predicates and instruction descriptors. |
| Vendor vector/custom DSP | Implementation-specific | Plugin capability with explicitly validated ABI and assembler/encoder, not a generic RVV alias. |

**Important:** VLEN is *register capacity*, VL is *active elements for an instruction*, and LMUL groups registers. Do not set vector-factor = VLEN/element width as a constant. LMUL selection is target-lowering metadata; check register pressure and legal combinations. Tail/mask-agnostic inactive lanes are not implicitly deterministic zero values; lower `zero`/`merge`/`agnostic` explicitly in the semantic IR.

### 5.4 Shared operation classes

Use operation traits/capabilities rather than "SSE4 vs NEON equivalent" hardwiring:

| Semantic operation | Scalar fallback | CPU fixed | CPU scalable | GPU |
|---|---|---|---|---|
| Add/sub/mul, integer bitwise | When implementable | SSE/AVX/NEON | SVE/RVV | Per-thread scalar or packed vector |
| `load`, `store`, strided access | When implementable | Aligned/unaligned; ISA-specific gathers | Predicated/active-length | Global/coalesced/local memory, separate address spaces |
| Compare and `select` | Branch/select | Lane masks/bitselect | Predicate registers | Per-thread control or subgroup ballots |
| Saturating/narrowing/widening | Scalar checked ops | Available extension-dependent | Available profile-dependent | Device/SPIR-V capability-dependent |
| Shuffle/permute, table lookup | Scalar | Multiple unrelated ISA encodings | Native or synthesized | Subgroup shuffle/shared-memory or per-thread vectors |
| Reduction/scan | Defined order | Tree/serial accumulator | Predicate-aware strip mining | Subgroup/workgroup reduction, synchronization |
| Gather/scatter | Ordered scalar | Feature-dependent | Feature-dependent | GPU memory ordering and collision rules matter |
| Crypto/dot/tensor | Portable fallback | AES/VAES/VNNI/AMX/NEON crypto/I8MM | RVV crypto / SVE/SME | Cooperative matrices/tensor hardware |

Maintain per-operation legality, cost, semantics and lowering; a generic "supports SIMD" flag is insufficient. GPU execution/subgroup distinctions follow their own API contracts. [E13][E14]

**Reference basis:** GCC documents independent x86 feature controls and the difference between ISA selection and tuning; Linux documents OS-enabled XSTATE. Arm ACLE distinguishes NEON, SVE, SME and MVE. The RISC-V V specification defines VLEN/ELEN, active length and register grouping; Qualcomm documents HVX as a Hexagon coprocessor extension. These motivate the grouping; they do not establish that Simple has completed every row. [E01][E02][E05][E06][E07]

**Implementation rule:** do not create one copy of a loop analysis for each row above. One semantic operation table delegates to family-specific lowering and cost descriptors. Advanced matrix features remain separate optional facets rather than being smuggled into the ordinary vector-width field.

## 6. ABI, 32/64-bit and OS separation

### 6.1 Five independent layers

| Layer | Common code | Per-target code |
|---|---|---|
| Language semantics / type system | Integer overflow and signedness, FP strictness, vector shape, mask/tail, memory safety | None; differences must not change portable source meaning silently. |
| Vector and parallel IR | Legality, dependency/alias reasoning, operation descriptors, region graph | ISA-specific legality and cost table; SIMD vs SIMT/tile scheduling. |
| Machine ISA | Target-independent instruction selection interface, generic register constraint model | x86 EVEX/VEX, ARM NEON/SVE/SME, RVV `vsetvl`, GPU PTX/SPIR-V/MSL/WGSL. |
| **Calling ABI / data layout** | Function signature graph, parameter ownership/marshal plans, layout verifier | System V AMD64 vs Win64 vs AAPCS64 vs RISC-V ILP32/LP64; vector-PCS rules; varargs, unwind, stack, struct return. |
| OS and runtime API | Canonical SOSIX service semantics and existing task/ring lifecycle | Native syscalls, wait/driver APIs and OS register-state authorization; loader policy and object parsing remain loader/compiler-owned. |

The existing Simple target and environment descriptors provide the integration seam for these differences. [R01][R17][R29]

**Do not confuse ABI with ISA:** AVX-512 may optimize a body while external function arguments still use the same platform ABI. Inlining and private internal ABIs can use vector registers. Public SFFI/FFI must remain conformant to the explicit external ABI.

### 6.2 ABI compatibility rules

- Public entrypoints and dynamically loaded module boundaries use a **stable scalar/buffer ABI** where practical: a typed buffer reference or a process-local pointer plus length/stride where the selected ABI explicitly allows it; pass vector values through memory where the external calling convention does not guarantee a compatible register ABI.
- `FixedVec` can be a monomorphized internal value; its external ABI is allowed only when the calling convention and vector type classification are proven.
- `ScalableVec` and scalable predicate values should be **function-local/IR-local** by default; prohibit storing in ordinary fixed-layout structs, taking `sizeof`, or crossing generic FFI boundaries unless an explicit scalable-vector PCS is selected and implemented.
- For RISC-V, qualify the exact baseline or vector calling convention against its versioned psABI before enabling vector-valued external calls. Do not infer that choosing RVV authorizes a vector-argument ABI.
- For SVE/SME, OS thread state and procedure call standard must be respected; support streaming-mode changes only with correct save/restore and stack/PCS rules.
- Kernel/device ABI includes resource argument binding, address spaces, layout/packing, alignment and shader/workgroup entry conventions. Queue submission and resource lifetime are runtime service contracts, not argument-passing ABI. **It is not the host CPU C ABI.**
- `SimpleOS` and bare-metal targets can choose a frozen Simple ABI, but changes require a versioned ABI contract and old-runtime compatibility check. The existing SimpleOS ABI v1 owner remains authoritative.

### 6.3 32/64-bit and OS variation

**Hard architecture effects:** `usize`/`isize`, pointer width, data layout, type alignment, integer legalization, atomics, code-relocation models, address-space widths, unwind tables, user/kernel mode. For 32-bit Windows x86, Win32 calling conventions differ from 64-bit Win64. RISC-V ILP32 vs LP64 varies integer and pointer ABI; an RV64 CPU may support a 32-bit userspace ABI only if the OS/toolchain actually does.

**OS effects:** Linux vs FreeBSD vs macOS vs Windows vs SimpleOS; executable format, TLS, syscall ABI, dynamic loading, threads/async backend, CPU-feature probes and GPU driver availability. `os=none` for bare metal must suppress unsupported host APIs. A build host's `PATH` separator or filename extension does not necessarily belong in code compiled for a different runtime OS. Preserve the existing distinction between build-target module overlays and runtime-host choices.

### 6.4 Boundary records are not host structs copied to the GPU

Reuse the existing environment and SOSIX fixed-width descriptors. Validate schema size/version, byte order, range, alignment and pointer conversion at each boundary. A cross-process/device message carries resource IDs plus generation, offsets and lengths—not a raw host address or a C++/Simple object graph.

A 64-bit offset can be meaningful on a 32-bit host, but converting it into an address requires checked arithmetic and range validation. The transport codec must not use implicit `usize` layout. Host/device layouts may differ; one layout planner emits adapters and a layout digest that both sides validate. Do not silently reinterpret a host `Vec3`, boolean, packed struct or opaque handle in a shader language.

`abi_digest` and `resource_layout_digest` are already descriptor fields. Use them for boundary validation instead of adding a private GPU packing hash with different rules. [R01]

### 6.5 Error domains must remain distinguishable

SOSIX's portable error kind is shared; native error numbers and API-specific status live in the native-domain payload. A Linux errno, Win32 error, CUDA result and Vulkan result must not be normalized by one unqualified integer lookup. Each native adapter supplies its domain and concrete code; shared normalization maps a specified `(domain, code)` pair into the portable kind.

Existing SOSIX mappings and v1 negative-status conventions must be preserved or changed through explicit compatibility adapters. In particular, a raw facade returning `-errno` is not an exact alias of POSIX's `-1` plus thread-local errno contract. The final design must correct that terminology before claiming zero-wrapper POSIX conformance. [R04][R06][E12]

## 7. Shared vectorization and GPU planning

### 7.1 Separate the common analysis from two execution models

```text
                        Simple source
                   attributes + CLI/SDN policy
                               |
                       frontend / typed HIR
                               |
                         canonical MIR
                               |
         effects + ownership/alias + iteration space + layout
                               |
                   Parallel-region analysis / vector plan
                        (target independent)
                               |
                  legality + profitable candidates
                           /          \
                   CPU SIMD            GPU compute/offload
                /        \              /       |        \
             Fixed     Scalable     Thread     Subgroup     Tile
           SSE/AVX    SVE/RVV     CUDA/Metal  Vulkan     GPU matrix ops
             NEON                 HIP/OpenCL  WebGPU
                \        /              \       |        /
                ISA lowering              backend emitter
                    |                   + existing executor integration
             CPU machine object        PTX/SPIR-V/MSL/etc.
                    \                       /
                      runtime dispatch/receipts
```

**Key invariant:** the shared parallel-region analysis describes **what** is computed, memory effects, dependencies, ordering and legal substitutions. The backend planner decides **how** (vector lanes, strip mining, GPU grid/workgroups, synchronization, tiling). Reuse the `ProcessingIR` direction documented in the existing processing backend guide. Keep the proposed `FixedVec`/`ScalableVec` direction consistent with `simd_unified_architecture.md`, but do not force GPU SIMT registers to impersonate CPU `FixedVec` values.

### 7.2 Suggested IR record

```text
ParallelRegion {
  id, source_span, iteration_domain, affine_indexes?, op_dag,
  input/output memory regions, address_spaces, alignment, strides,
  alias_proof, ownership_proof, side_effects, synchronizations,
  integer_overflow_policy, fp_mode, ordered_reduction, scatter_collision_policy,
  permitted_execution_domains, candidate_shapes, debug_receipt_id
}
VectorPlan {
  provider_id, required_feature_ids[], mode: fixed|scalable,
  element_type, min_lanes, vector_factor?, unroll_factor,
  active_mask_policy, tail_plan, alias_guard, fallback_region,
  estimated_cost, validation_state
}
GpuPlan {
  api, device_id, kernel_signature, grid, workgroup_shape,
  subgroup_requirements, memory_transfer_plan, fusion_groups,
  tile/matrix_plan?, barriers, queue/sync_plan, cpu_fallback,
  estimated_cost, validation_state
}
```

These are conceptual views over the existing MIR/ProcessingIR plan and evidence owners, not instructions to introduce a second graph or parallel public schema. Serialize an existing owner's plan as SDN or versioned compact binary when needed. A compiler inter-pass structure should use typed fields/enum IDs, not runtime text comparisons. Do not construct full candidate sets unless optimization level requests them.

### 7.3 CPU vectorizer legality and enhancements

Implementation starting point: the currently inspected optimizer and rewriter, not a second vectorizer. [R20][R22][R26]

1. Reuse `auto_vectorize_analysis`, `validate`, `alias`, `cost`, `_AutoVectorize/rewrite` as the authoritative pipeline. Inject the existing target-codegen profile; do not create a competing optimizer coordinator.
2. Separate **legal operation** from **supported ISA lowering** from **profitability**. A legal scalar loop can remain scalar if no backend or if vectorization loses performance.
3. Expand from currently narrow fixed-lane elementwise addition/multiplication to subtraction, compares/select, casts, byte loops, reductions, segmented loads, scalar prolog/epilog, masked tails and *dynamic* trip counts. Gate each transformation on its own differential oracle and rollback path.
4. Integrate `55.borrow` or existing provenance facts to prove noalias. When not proven, insert pointer-range guards plus an intact scalar loop, with overflow-safe ranges and per-access consideration. Never assume distinct locals imply distinct memory.
5. Implement **loop vectorization** first, then **SLP vectorization** (straight-line independent scalar statements), interleaving and outer-loop vectorization. Share legality helpers but different pattern matchers.
6. Add a target cost interface: throughput, latency, vector register pressure, downclock effect, mask/gather cost, setup (`vsetvli`), code size, branch prediction and cache effects. Compare the supported, legal subset of scalar/128/256/512 candidates on x86; choose a **scalable** plan for SVE/RVV. Never construct a candidate that the output target cannot lower.
7. Preserve strict integer overflow, NaN behavior, signed zeros, deterministic FP and order-dependent reductions unless the user explicitly opts into relaxed math. No generic unordered scatter when duplicate indices could alter the winning write.
8. Dynamic tails: fixed vectors use masked load/store where available or a scalar epilogue; SVE/RVV use predicate/`vl` loop. Never mistake RVV tail-agnostic lanes for zero-filled portable values.
9. Keep compile-time analysis bounded: bounded shared dominator/dataflow setup reused across loops, recipe cache keyed by MIR fingerprint and relevant feature set, expensive SCEV/alias optimization only at higher levels.

### 7.4 GPU: deeper parallelization, not just wider SIMD

A GPU workload is not automatically an AVX-512 loop with a larger width. CUDA SIMT and Vulkan subgroups have distinct control/synchronization contracts. [E13][E14] Potential GPU-specific transformations:

- **Many independent iterations:** map iteration to thread IDs, select grid and workgroup, coalesced layout and register-private state.
- **Kernel fusion:** combine adjacent maps/filter/elementwise ops to avoid extra launch and global-memory intermediate buffers.
- **Tiling:** shared/local-memory reuse in matrix/image operations, halo handling, warp/subgroup layout.
- **Hierarchical reductions/scans:** per-thread → subgroup → workgroup → global; explicit barriers/atomics as needed.
- **Subgroup collectives:** CUDA warp (normally 32); Vulkan subgroup size and supported ops queried; Metal exposes `threadExecutionWidth` on the compute pipeline state. Query the appropriate API property; never hardcode one cross-GPU width. [E16]
- **Tensor/cooperative matrix:** explicit subfeature/shape query (CUDA tensor cores, Vulkan cooperative matrices, platform metal matrix capabilities where available); scalar/fallback kernel must remain correct.
- **Data residency:** only offload when legal and net throughput wins after transfers, allocation/launch, synchronization and device contention.
- **Async GPU submission:** bind the existing SOSIX operation, ring/task and Future contracts; avoid hidden blocking in the hot path. CPU direct pointers must not become GPU device pointers without an explicit compatible memory/coherency contract.

**Suggested cost heuristic:**

```
CPU_cost = cpu_setup + N * cpu_cost_per_element
GPU_cost = host_to_device + launch + N * gpu_cost_per_element
         + device_to_host + sync + allocation_cost
eligible = legality AND device_admission AND permitted_effects
select_GPU = eligible AND
    (explicit_required_GPU OR GPU_cost * risk_margin < CPU_cost)
# Residency changes GPU_cost; it does not bypass legality or policy.
```

Cost values are profiled/estimated, not invented constants. Cache per operation shape/device/driver/version and preserve a conservative initial threshold. Use overlapping transfer/execution only when dependencies permit. `--compute=require-gpu` should fail with a reason if no valid device plan exists.

### 7.5 Backend shared/specific responsibilities

| GPU part | Shared compiler/runtime code | Backend-owned specifics |
|---|---|---|
| Kernel eligibility | Effect checker, memory alias legality, supported operation catalog | Per-API instruction legality, supported types and shader stage constraints |
| Algorithm | ParallelRegion, fusion/reduction/tiling planner | Subgroup shape, occupancy and device-specific tile cost |
| IR to artifact | Kernel signatures, typed buffers, artifact hash/signature, cache | PTX/CUBIN via CUDA, HIP/ROCm objects, SPIR-V for Vulkan, MSL/metallib for Metal, OpenCL C/SPIR-V, WGSL for WebGPU |
| Dispatch | Device selection contract, command graph, synchronization requirements | CUDA streams, HIP queues, Vulkan queues/pipelines/descriptors, Metal command buffers, WebGPU encoders |
| Memory | Ownership/transfer planner, lifetimes, data residency | Host/device/pinned/unified/device-local coherency, resource barriers and allocation APIs |
| Error/evidence | Common diagnostic code + actual execution receipt | Validation layers, driver/compiler logs, device event timing, artifact verification |

**Do not merge `PortableComputeTarget` and runtime API adapters prematurely.** First normalize all current enums (including the separate Vulkan lane) into the existing registered device API IDs, then de-duplicate source/launch contracts by executable tests. The portable CPU implementation supplies the reference where the contract permits it; an explicit required GPU plan does not silently fall back.

### 7.6 Common analysis without an oversized universal IR

Retain one source/HIR/MIR pipeline. Attach a compact parallel-region summary to the existing optimizer: iteration space, access/effect summaries, numerical mode, alias evidence and candidate recipe IDs. CPU and GPU lowerings consume that summary. Do not clone MIR into a second graph merely because a GPU candidate exists, and do not merge GPU barriers into an ordinary CPU-vector value type.

Loop dependence, bounds facts, reduction contracts and fusion legality are shared. Register pressure, RVV LMUL, SVE predicate selection, CUDA occupancy, Vulkan subgroup constraints and Metal resource binding remain target-specific. SLP matching and loop matching may be separate algorithms, but must reuse their common analyses rather than duplicate them. LLVM's documented separation of loop/SLP vectorization and profitability checks is useful prior art, not a requirement to reproduce LLVM's entire pass stack. [E08]

### 7.7 Preserve exact effects, including traps

“Same final output” is not sufficient for an effectful operation. A vectorized loop must preserve required trap/error order, observable writes, bounds checks and integer-overflow behavior. A wide load past the logical end is forbidden even when the masked output would be unused. If a checked arithmetic trap would occur after earlier scalar writes, speculative GPU or SIMD execution cannot silently change that observable contract.

Default transformations target pure/bounded kernels with validated buffers and well-defined publication. Relaxed FP, unordered reductions and unique-scatter assumptions require explicit proof or requested policy. Exact base aliasing is safe only for access patterns the dependence analysis actually proves; it is not a universal exception for every stencil or recurrence.

### 7.8 Generated specialization, not copied algorithms

A single portable map body can produce SSE2/AVX2/AVX-512/NEON/RVV code and GPU kernel variants. Keep its semantic identity and source digest stable across these outputs. A backend-specific optimized schedule or intrinsic substitution references that same operation contract. Static bounds, checks, result publication and portable errors are authored once.

Avoid promising that every ordinary scalar loop is automatically offloadable. Some operations need device-specific kernels or have no profitable/safe device plan. Emit an explicit missed-optimization reason instead of generating a dummy kernel or changing semantics.

## 8. Options, tags and enforceable evidence

### 8.1 Recommended policy

Existing syntax/receipt and GPU metadata owners are the compatibility baseline. The policy below is the proposed completed contract. [R21][R24]

- **Default** for release builds: try safe profitable **CPU SIMD** auto-vectorization. Debug builds can stay scalar by default or use a debug-friendly vector tier; be explicit in config. Interpreter can execute portable MIR vector semantics or select a real runtime SIMD kernel, not claim native SIMD from metadata alone.
- **GPU offload**: explicit GPU kernels remain explicit. Auto-extraction of scalar loops to GPU is separately enabled and cost-gated; default to CPU unless caller opts in, data is already device-resident, or the library operation has a qualified GPU variant with a defined `auto` policy.
- **Tags** communicate local constraints, not a replacement for global flags. An ordinary loop should need **no SIMD tag**. Respect existing `@simd(disable)` / `@must(simd)` / `@prefer(avx512)` contracts and existing `@gpu_kernel`/`@vulkan_kernel` entrypoint syntax. Avoid inventing a second `@vectorize` grammar.
- **`@must(simd)`** requires a qualifying vector rewrite/lowering and emitted-code evidence for the designated region, not mere pattern recognition; execution evidence is a separate runtime/test stage. **`@prefer(avx512)`** is a hint with a warning/receipt on nonselection. GPU requests use their own typed execution-domain receipt.
- A source-level **`@when`** is for compile-time target selection of a code path/import, never a substitute for runtime ISA probing or GPU availability. It should consume typed target/enum predicates, not string comparisons. Keep it orthogonal to overlays.

### 8.2 Proposed CLI/SDN policy (illustrative; new switches require implementation)

```text
simple build app.spl --target=<triple> \
    --target-cpu=x86-64-v3 --target-features=+avx2,+fma \
    --vectorize=auto --compute=cpu

simple build app.spl --target=<triple> \
    --vectorize=aggressive --compute=auto --gpu-backend=vulkan,metal,cuda

simple build app.spl --target=<triple> \
    --vectorize=off --compute=cpu
```

Existing `--target-features` and `--var` mechanisms should be reused. `--vectorize`, `--compute`, and `--gpu-backend` are **proposed policy spelling**, not claimed current CLI support. Suggested policy defaults:

```sdn
# PROPOSED config/compute.sdn
compute:
  vectorize: auto       # off | auto | aggressive
  simd_max_width: auto  # fixed-vector plans only: auto | 128 | 256 | 512
  fp_mode: strict       # strict | relaxed (explicit opt-in)
  gpu: explicit         # off | explicit | auto | require
  gpu_backends: [vulkan, metal, cuda, hip, opencl, webgpu]
  allow_runtime_dispatch: true
  prefer_small_binary: false
  prohibit_implicit_transfer: true
  receipt_level: normal # off | normal | analysis
```

The proposed `simd_max_width` limits fixed-vector candidates, not the hardware VLEN or a GPU subgroup width. Scalable code normally remains vector-length-agnostic; any fixed-VL tuning requirement belongs to an explicit admitted worker/codegen profile. `gpu: auto` must still respect `prohibit_implicit_transfer`; it cannot silently override that policy because a GPU was discovered.

Use enum values in compiler data structures; map text to enum exactly once at CLI/SDN input. Unknown feature, ambiguous backend or impossible cross-target capability is an error; do not silently ignore spelling mistakes in new strict target-profile logic. If a multi-target list contains features for several architectures, require an explicitly scoped feature namespace.

### 8.3 Three separate forms of dispatch

1. **Compile-time selection:** one module or one native ISA lowering for a known deployment target; zero runtime dispatch cost.
2. **Function multiversion dispatch:** emit scalar + ISA variants and choose once at loader/function boundary. Use cached function pointer/direct trampoline/IFUNC only where OS supports it; no repeated CPUID in a tight loop. Target-specific ABI must be identical at the public boundary.
3. **Device/operation dispatch:** choose compute backend from device-capability + data-residency + cost; cache compilation and prepared pipelines. Do not enumerate GPUs on every call.

Manual selection/downscope is allowed. Production runtime overrides cannot fabricate hardware or OS-state capability. Cross-build ISA declarations are not runtime overrides; unsupported local execution remains rejected. Prefer a diagnostic explaining why a requested native path cannot execute.

### 8.4 Requirement meaning and precedence

Keep existing spellings until compatibility is specified. Parse them once into typed policy. A per-region `must` is an acceptance requirement, a `prefer` is an optimization preference, and `off` is a prohibition. Contradictory hard constraints are diagnosed; they are not resolved by whichever file happened to load last.

An ISA requirement and a vector-width requirement are different. AVX-512 can include shorter EVEX operations when the necessary extensions exist; therefore the new typed representation must distinguish `requires ISA feature set` from `requires 512-bit lowering`. The current receipt's width-based checks need explicit migration tests and documented legacy behavior. A NEON rewrite must not satisfy `must(avx2)` merely because its aggregate work processes 256 bits. [R21]

A compile-time `must(gpu)` can require an accepted GPU artifact; runtime `require-gpu` additionally requires a usable device and successful admission. Do not require a GPU on every cross-compilation machine merely to produce an artifact. Source-level enforcement uses the existing typed diagnostic path through optimizer and driver; emitting the word `error` to stderr is not sufficient unless the build exits with failure and withholds its success artifact.

Integrate the previously planned target-aware enum predicates in `@when` and TLDR imports; this report does not claim their complete current implementation. Keep runtime device availability separate. No new prefix or grammar is needed merely to isolate variations.

## 9. SOSIX consolidation contract

### 9.1 Unify contracts and the library, not every provider

SOSIX remains the OS-service boundary for the compiler, interpreter, ordinary libraries, UI and SimpleOS clients. Its shared contracts already cover operation IDs, capability/buffer references, completions, wait behavior and service IDs. Hosted composition and SimpleOS bind those contracts to different providers. Reuse the existing `SimpleRing` and task vocabulary instead of wrapping it in a new target-variation operation envelope. [R04][R06][R07]

```text
                  application / compiler / interpreter / UI
                                    │
            shared algorithms       │       explicit host effects
        (ordinary direct calls)     │                │
                                    │          SOSIX service API
                                    │                │
                           canonical operation + task/ring contracts
                                                     │
                              admitted service provider, bound once
                                  /          |              \
                         hosted OS      SimpleOS provider    device proxy
                                                     │
                                      native completion / lease retirement
                                                     │
                                          canonical task/Future result
```

**SOSIX does not own:** SIMD math, parser algorithms, HIR/MIR, vectorizer costs, tensor/DrawIR semantics, object-file parsing, loader admission policy or collection algorithms. **SOSIX does own the boundary for their host effects:** file/network access, time/input/display services, memory mappings, dynamic-library mechanisms and qualified device resource operations. This preserves consolidation without turning it into an oversized compulsory runtime. [R04]

### 9.2 Existing contracts and concrete reuse

| Need from the variation design | Use the SOSIX/consolidation owner | Do not add |
|---|---|---|
| Operation identity | `SosixOperationId` lifecycle, with existing typed device-handle projections correlated to it | An independent public operation lifecycle or unrelated global operation namespace |
| Submission token | `RingToken`, `RingGeneration`, `RingAdmission`; existing SOSIX-G sequence/epoch fields at the wire boundary | An independently evolving token/state protocol with no authoritative mapping |
| Pending work | `TaskPollResult`, `TaskContext`, existing task frame/bridge | a new Promise implementation per backend |
| Buffer lifetime | Existing SOSIX buffer references plus `RingPayloadLease` mapping | GPU-private public ownership rules unrelated to SOSIX retirement |
| Completion | Existing completion record and portable/native error split | separate CUDA/Metal/Vulkan public result lifecycles |
| Waiting | Existing spin-free sync adapter and executor wake integration | `.wait()` inside every provider's `poll` method |
| Service identity | Existing frozen `service_ids_v1` | application-local integers for file/display/timer services |
| Direct/native transport | Existing mapping/admission grades with actual evidence | a new “direct” boolean inferred from API name |

Backend-native handles and command/fence objects may remain private. The table forbids competing lifecycle authorities, not the state an operating system or GPU API requires internally. In particular, the existing SOSIX-G design already has `GpuOperationId`, request/completion wire records and a backend manifest. Keep those typed transport projections with an explicit correlation to the canonical operation; do not delete them merely because their byte layouts differ from an in-process `RingToken`. [R09]

### 9.3 Async-first without copying sync implementations

For potentially blocking services, implement one submitted operation and one completion/retirement path. The async facade polls or awaits that operation. The typed sync facade submits the same operation and uses the existing wait adapter. It must not contain an independently implemented synchronous file or GPU algorithm.

Cheap synchronous leaves remain direct: monotonic-time reads, capability checks, already-available queue inspection and in-memory arithmetic need not manufacture Futures. No-GC is not synonymous with no allocation; distinguish unrestricted no-GC allocation, `mission_alloc` bounded arenas and `mission_pool` fixed capacity. Each provider advertises its resource contract and fails before submission when that contract cannot be met.

A fallback provider that executes blocking host calls can service them on an explicitly allowed bounded worker. It must not block a UI executor, GPU completion pump, device kernel or cooperative poll callback. Its capability report says worker-backed/synchronous-native, not native async. The current portable SOSIX file driver demonstrates why this distinction matters. [R05][R06]

Canonical Future/Promise owns paired result publication and wake rules. Backend events map into it through existing task adapters. GC families re-export or add ownership-safe allocation facades; they must not maintain independent result state machines. Sync compatibility adapts the same result, rather than copying Future code.

### 9.4 Exact POSIX aliases: an optimization, not a semantic shortcut

Choose a direct symbol alias only after proving all of the following for that specific operation: calling convention, argument widths, pointer domain, ownership, return/error behavior, blocking/cancellation semantics and applicable security policy. A signature that looks similar is insufficient.

The currently documented raw positioned facade returns bytes or `-errno`, so it is a typed/raw adaptation—not the POSIX `-1` plus errno interface. Linux also documents an `O_APPEND` difference for `pwrite`; preserving native Linux behavior and offering portable positioned semantics are different contracts. A portable operation can reject incompatible descriptor modes or use a qualified alternative; it must not silently toggle flags on a shared descriptor. [R06][E12]

Where exact aliasing is valid, eliminate forwarding with the supported re-export mechanism and verify generated code. Where it is not, keep one narrowly owned adapter. Do not duplicate adapters in each library family, and do not call a wrapper-free path “zero cost” without inspecting the emitted call boundary. The SOSIX design's later braced-alias candidate remains subject to its stated native/interpreter qualification. [R04]

### 9.5 One operation lifecycle; separate logical completion from retirement

Do not replace the existing state machine. Extend its admission/retirement hooks only through its owner. Use the following conceptual obligations to test that implementation:

```text
logical result:     pending -> terminal success / failure / cancellation / timeout
native work:        admitted -> submitted -> still-accessing-resources -> retired
consumer ownership: retained -> observed/released
reuse allowed:      terminal AND provider-retired AND consumer-release-complete
```

A timeout or cancelled Future can become logically terminal while native I/O or GPU work still owns a buffer. Cancellation request success is not by itself proof that all device/kernel accesses are finished. Observe the relevant native terminal/retirement signal before reusing memory; release the exact token and generation, once. Linux io_uring cancellation documentation distinguishes the cancel operation from its target, and Vulkan synchronization similarly makes device completion explicit. [E09][E10]

Preserve retained completions, out-of-order release and generation-exhaustion behavior from the existing SOSIX design. A generation that would wrap and permit a stale handle to alias a new operation must fail closed. Reset/drain/unload is not allowed to free provider state while an old operation or callback can still reference it. [R04]

### 9.6 Host-service boundaries for compiler, interpreter and loader

Inject the same admitted SOSIX service facade into compiler driver, interpreter and loader host-effect adapters. Parser tokenization and SIMD classification remain pure/direct. Source file reads, environment access, subprocesses, dynamic libraries and executable mappings use the host-service boundary.

Loader **policy** stays in the loader: artifact identity, trust, dependency resolution, ABI compatibility and entrypoint admission. OS `dlopen`/mapping/protection mechanisms stay behind native services. Avoid the cycle “load SOSIX through a loader that requires SOSIX to load itself.” Link a minimal static baseline for startup/probe/mapping/bootstrap, then publish optimized bindings after admission. This bootstrap provider obeys the same contract and is not a second loader.

A native SIMD provider might be usable without any OS calls. Its call remains direct. Only its optional dynamic loading and environment setup use SOSIX.

### 9.7 SimpleOS and bare-metal remain real provider targets

Reuse the existing SimpleOS positioned-service stack, ABI v1 and host-service IDs. Do not add a separate SimpleOS file implementation merely to match hosted names. Existing legacy routes retire only after trap, linker, registration and live behavior are proven; historical source guards or model tests do not satisfy that gate. [R05][R08]

Bare-metal profiles select only their admitted service subset and fixed-capacity executor/transport. Unsupported networking, filesystem, dynamic loading or accelerator services return typed unavailability; a fake POSIX or GPU stub must not return success. Kernel SIMD use also needs a qualified context-save/preemption/interrupt policy; user-mode capability detection alone does not authorize it.

### 9.8 Error mapping and service descriptors have one owner

Keep one canonical portable error vocabulary and service table. Native adapters contribute domain-specific mappings without altering meanings for individual callers. Preserve partial progress and distinguish retryable, terminal and unknown-completion failures. Neither a GPU backend nor a variant selector invents new file-service numbers.

A service extension uses the current registry/versioning process. Until its IDs are allocated, examples in this proposal name the desired facet symbolically and do not assign speculative numeric IDs. Generated headers, dispatch tables, Rust/C bridges and documentation come from that single definition.

## 10. GPU execution through SOSIX without duplicate runtimes

### 10.1 Split three responsibilities

| Responsibility | Shared owner | Provider-specific work |
|---|---|---|
| Compute semantics and planning | Existing MIR/ProcessingIR/portable-compute owners | instruction/type availability, kernel ABI and target schedule |
| Operation and resource lifecycle | SOSIX + existing SimpleRing/task/Future contracts | correlate native submission and completion; retain native resources |
| Native API translation | Existing qualified CUDA/Metal/Vulkan backend owner | CUDA stream/event/module calls; Vulkan queues/descriptors/barriers; Metal command encoding and resource options |

Register separate compiler and runtime facets when both are needed. CUDA compilation need not load a CUDA runtime during an ordinary CPU build; binding a GPU runtime does not authorize a compiler to emit every device instruction.

Different APIs retain genuinely different memory and synchronization rules. CUDA documents stream-ordered asynchronous work; Vulkan explicitly manages queue/memory dependencies. A common lifecycle adapter must encode those dependencies, not assume an event/fence name makes their semantics interchangeable. [E10][E11]

### 10.2 Host submission path

```text
shared operation / generated kernel
  -> prepared execution plan (no rediscovery)
  -> existing SOSIX operation and resource leases
  -> bound CUDA | Metal | Vulkan provider
  -> native queue/command submission
  -> native event/fence/completion observation
  -> memory visibility and resource retirement established
  -> canonical task result / Future wake
```

Do not add an extra software ring around an existing efficient submission route solely for architectural symmetry. Where direct mapping to the existing ring contract is qualified, preserve it. Otherwise use a translated/software provider with an accurate grade and measured cost. One logical submission may legitimately produce multiple native commands; it must not create an unrelated public operation lifecycle for each backend.

Common resource/transfer planning is shared above the adapter. A CUDA provider may use private memory pools, and a Vulkan provider may manage private descriptor pools; these are real API differences. Neither duplicates the portable buffer ownership model or decides independently whether a library algorithm should fall back to CPU.

### 10.3 Device-initiated SOSIX-G is a projection, not a second SOSIX

A device kernel cannot import the full host SOSIX library. Preserve the existing SOSIX-G checked execution profile, service-ID/effect metadata and restricted, pre-authorized device library. The GPU-side request refers to resource handles, generations and bounded byte ranges. The host proxy validates and correlates it with the canonical service operation; it does not introduce another operation-state authority. [R09]

| Existing SOSIX-G tier | Keep this distinction | Qualification boundary |
|---|---|---|
| G0: GPU-local | Bounded queue/poll/trace/input/pool operations | Device-local legality, capacity and memory ordering |
| G1: host-proxied | Authorized operations on pre-opened files/sockets, handle metadata and IPC | Qualified request/completion transport, rights checks and host service provider |
| G2: direct-data or device-initiated | Payload path and request-initiation guarantees are separately reported | Device/driver/memory/coherency and exact direct-mode evidence |

Retain the established `SosixGpuRingControlV1`, `SosixGpuRequestV1`, `SosixGpuCompletionV1` and `SosixGpuBackendManifestV1` design contracts. Their sequence/epoch fields and fixed-width wire layout are a necessary transport projection, not permission to duplicate SOSIX semantics. Use the same declared contract hash, generated codec/layout artifacts and version negotiation. Do not replace these records with a copied host struct or change a frozen v1 layout casually. Their presence in a design report is not a claim that every provider implements them. [R09]

Keep compiler-owned `@sosix_api` keys and flags under their existing authority. Extend the shared execution-contract/call-graph checker and backend manifest validation to each supported backend; do not add a private CUDA validator, Metal validator and Vulkan validator with different effect meanings. Source overlays or ordinary extension methods grant no additional device rights. Static metadata is checked at compile/link time; actual device/API/transport admission happens again at deployment. [R09]

Do not allow arbitrary path open, DNS, process control, host VM operations or device-side dynamic loading through the v1 device profile. Pre-authorized handle operations remain available only through their declared tier. A proxy may delegate blocking work to an allowed bounded host worker; the completion pump stays nonblocking. Device waiting uses the existing nonblocking/bounded cooperative or continuation policy, never an unbounded ordinary host-style wait. Preserve batching and subgroup/workgroup coalescing rather than emitting one service request per lane. [R09]

Preserve existing `GpuIoPreference` distinctions: `Proxy`, `DirectPreferred`, `DirectRequired`, and `DeviceInitiatedRequired`. A direct payload path is not evidence that the GPU issued its control plane. A required direct/device-initiated mode must reject an insufficient provider instead of silently staging through a proxy. Keep existing `CpuReference`, `HybridVectorGpu`, `ResidentGpu` and stage-fallback policy vocabulary rather than inventing equivalent profiles. [R09]

Device-initiated NVMe/NIC/native queues are not implied by CUDA, Vulkan, Metal, RVV, unified memory or a ring type. Require evidence for mapping permissions, atomic/coherency scope, ordering, device/driver support and doorbell visibility. G1 qualification on CUDA does not automatically qualify G1 on Vulkan or Metal: use each API's actual memory/atomic contract, otherwise report the transport unavailable while keeping ordinary host-launched GPU compute available.

### 10.4 Async hazards and fallback policy

| Situation | Required behavior |
|---|---|
| No compatible GPU before submission | `auto` may choose an allowed CPU plan; `require-gpu` errors. |
| Transfer/kernel allocation fails before effects begin | Release reservations; select a permitted fallback only with consistent resource state. |
| Timeout/cancel after native submission | Publish the requested logical result according to contract, retain native resources until retirement. |
| Device loss with uncertain partial writes | Return an explicit uncertain/failed operation status; do not run the CPU algorithm blindly over potentially modified output. |
| Pure operation with isolated scratch output | Retry/fallback may be legal after old access is retired or safely isolated and result ownership is published through an atomic handle/swap or another proven transaction. Ordinary multi-element writes are not assumed atomic. |
| External side effects, non-idempotent writes, DMA or host service | Retry requires explicit idempotence/transaction proof; otherwise report failure. |
| Provider reload | Stop admitting new work to the old generation, drain retained operations and callbacks, then unload. |

Exactly-once execution cannot be manufactured by a single Future type. Distinguish at-most-once submission, duplicate-completion suppression, idempotent retry and transactional output publication in the operation contract.

### 10.5 Residency and scheduling stay shared, not centralized into one thread

Keep buffers resident when legal and profitable. The execution planner shares transfer/fusion decisions; the current task/executor infrastructure coordinates dependencies. Independent queues/workers remain possible. “One lifecycle” does not mean “one global locked queue,” “one OS thread,” or “one allocation arena for the whole machine.”

Use per-session or per-queue resource state with bounded operation storage. Do not allocate a new global backend-selection cache in every graphics, parser or tensor module. Cache prepared plans under the existing provider/session identity and invalidate them with its generation.

### 10.6 Rendering and compiler-GPU offload use the same boundary

Engine2D/DrawIR/layout remain renderer/library semantics. SOSIX supplies host input, display/present, timer and device-lifecycle services. Renderer selection composes a renderer strategy with a GPU runtime facet; it does not reimplement the CUDA/Metal/Vulkan resource manager. [R04][R10]

Compiler GPU tokenization or structural parsing follows the same device session and buffer contract, but preserves one grammar, source snapshot, parser-region format and CPU recovery path. Do not create a CUDA parser, Vulkan parser and Metal parser with independently edited grammar or token semantics. Algorithmic CPU/GPU differences are generated plans or isolated kernels under one frontend semantic owner.

## 11. Build, cache, bootstrap and hot-path performance

- **GPU-friendly front end:** no additional grammar is necessary. Parser builds stable AST/HIR once. Vectorization metadata is one parsed declaration attribute or CLI policy; do not scan raw source strings to recover `@simd` intent. Keep existing one-pass parsing architecture.
- **Early invariant checks:** target triple/ABI/width and typed `@when`/overlay selection can be resolved before heavy MIR optimization. GPU runtime selection is not a compile-time `@when` decision unless producing a target-bound artifact.
- **Independent cache layers:** (1) source tokens / AST, (2) typed HIR and generic MIR, (3) legality/ParallelRegion, (4) target-specific optimized MIR, (5) emitted machine/GPU artifact, (6) prepared runtime pipeline. A change from AVX2 to AVX-512 invalidates stages 4–6, **not** source parsing and target-neutral semantics if no static imports change.
- **Cache keys:** source content hash, declared target identity, ABI ID, feature mask, compiled provider/plugin version, vectorizer algorithm version, flags affecting FP/overflow/alias behavior, selected overlay file hashes, and GPU API/device properties for device-specific artifacts. GPU driver/toolchain version matters for compiled binaries and pipeline caches.
- **Avoid duplicate compile:** a multi-target bundle shares demonstrably target-independent MIR and legality analysis; generate only changed backend-specific fragments. SMF directory/bundle may hold `generic.mir`, `targets/<digest>/...`, `receipts.sdn` with stable indexing and atomic publication.
- **Lazy compile and dynload:** do not compile GPU kernels or AVX-512 variants on startup unless explicitly requested. Cache the prepared variant and perform admission before loading/executing ISA instructions that need unavailable state.
- **Hot path:** bitmask predicates, compiled direct calls and per-provider function pointers. No string matching, global registration, filesystem probes, CPUID/XGETBV or plugin lookups per vector instruction/loop iteration.
- **Memory:** cap specialized-code explosion with a budget and profile. `AVX2 + AVX-512 + NEON + RVV + 6 GPU APIs` should produce only relevant artifacts per target package, not every possible permutation.

The existing codegen factory already documents session-time selection rather than registry dispatch per MIR node. Preserve that design. [R30]

### 11.1 Cache projections, not one giant environment hash

Cache identity must include every relevant dependency without invalidating unrelated stages. Parse results depend on source, grammar and parser options. Typed HIR/MIR may also depend on static target predicates, `usize` layout, ABI-visible declarations or selected imports; do not claim universal cross-target sharing where those affect meaning. Separate target-neutral summaries from layout-bound results.

| Cache | Include | Exclude when irrelevant |
|---|---|---|
| Token / structural parse | Source bytes, grammar, dialect, parser version | GPU device identity, SIMD preference, OS I/O provider |
| Target-conditioned module resolution | Slot ownership, target-static predicates, selected source paths and content digests | Runtime GPU utilization |
| Typed / legality result | Semantic inputs, relevant target layout/effect facts, proven alias information | Unused installed ISA/GPU providers |
| Optimized code | Codegen profile, numerical contract, required feature set, lowering version | Arbitrary host feature changes in a cross-build |
| GPU binary / prepared pipeline | Kernel body/layout, target API/toolchain, required device features; driver/device keys where the native cache requires them | Unrelated file-service selection |
| Runtime binding | Admitted environment/catalog/policy generations and dependency lock | Source parsing caches |

The previous build-runner/IDE/Spipe editing and TLDR metadata plan remains the source of edit invalidation. This variation work consumes its source snapshot and dependency hashes; it does not add a second timestamp/edit-log service. Parsing on GPU or SIMD changes the producer implementation, not the identity of a semantically identical parse result.

### 11.2 Compile once, lower only where necessary

Share immutable source buffers, parsed modules, target-independent type facts and recipe summaries in the existing build-runner/session cache. Generate only the requested CPU/GPU artifacts. Do not compile an OS × ISA × GPU × ABI Cartesian product. A multi-target package may contain several target artifacts, but shared source/IR need not be duplicated in memory or in each plugin.

A changed SIMD preference invalidates the affected optimized code/binding, not every TLDR. A changed ABI/layout may invalidate more and must do so correctly. A selected overlay source change invalidates consumers of that slot, not every file that could hypothetically use the overlay root.

### 11.3 Performance constraints

| Path | Structural requirement |
|---|---|
| Pure scalar/SIMD operation | No SOSIX request, Future allocation, string lookup or capability probe added. |
| Monomorphic native lowering | Existing direct target traversal; no registry negotiation per MIR node. |
| Source resolver | Bounded relevant-slot lookup; no repeated scanning of absent variant roots. |
| Native host-service fast path | No extra queue crossing or full payload copy solely for consolidation. |
| Async completion | No blocking call in poll/pump; no general-purpose allocation after admission under a fixed-pool profile. |
| GPU execution | Reuse prepared device state; no module compile or GPU enumeration per small call. |
| Diagnostics | Format text lazily; full receipts/traces are opt-in or sampled, not per-lane. |
| Provider replacement | Generation check at controlled boundaries; no inner-loop lifetime registry access. |

These are acceptance constraints, not measured performance claims. Compiler setup may use bounded tables and validation; requiring every initialization step to have zero cost is neither necessary nor credible. Measure startup, warm compile, RSS, generated-code size and actual kernel throughput before changing defaults.

### 11.4 Profile tiers and heavy analysis

Keep low-cost correctness checks always enabled. Ordinary optimized builds use bounded loop analysis and a small candidate set. Deeper alias search, large fusion/tile exploration, whole-call-graph optimization and exhaustive clone scans belong in analysis/release qualification tiers. A hard user constraint is never silently ignored merely because its proof budget was exhausted: return a diagnostic or retain the safe unoptimized path according to the constraint.

`mission_pool` and `mission_alloc` publish budgets through the existing descriptor fields. When admission cannot satisfy them, fail early. A user-space GPU driver may allocate internally even when Simple code does not; do not advertise an end-to-end hard no-allocation guarantee without provider/driver evidence.

## 12. Enforcing isolation and preventing duplication

### 12.1 Machine-checkable ownership inventory

Extend the existing variant catalog, SOSIX route census and feature traceability records. Do not create a disconnected database. Each semantic slot records its contract owner, implementation sources, varying axes, provider dependencies, current users, compatibility aliases and retirement status. Human-readable Markdown/`variants/index.sdn` views are generated from these owners.

**Proposed record fields to map into existing SDN metadata:**

```sdn
ownership:
  semantic_slot: bitmap.and
  owner: existing_bitmap_contract_owner
  portable_body: existing_portable_implementation
  providers: [scalar, x86_simd, arm_simd, riscv_vector]
  allowed_variation: [isa, schedule]
  duplicated_semantics_allowed: false
  legacy_paths: []
  acceptance: existing_sspec_reference
```

This is a schema proposal, not a current runtime parser example. Actual IDs come from the established registry; paths must be discovered from the source tree rather than generated by naming convention.

### 12.2 Boundary checks

Run an import/effect graph check over **resolved imports**, not only source-text grep. It must catch aliases, transitive imports, generated wrappers and variant-selected modules. Check both default and explicitly selected profiles.

| Diagnostic class (proposed names) | Reject |
|---|---|
| `VAR-OWNER` | Two independently maintained owners for the same contract/lifecycle or an unowned new slot. |
| `VAR-LEAK` | Common semantics importing concrete OS/ISA/device implementations or performing host detection. |
| `VAR-SHADOW` | Overlay replacing a module outside its allowed slot/group. |
| `VAR-CYCLE` | Provider/composition/loader dependencies form a cycle, including bootstrap loading cycles. |
| `VAR-CROSS-TARGET` | Output code legality or static imports derived from the compiler host rather than output target. |
| `VAR-ABI` | Pointer width, ABI, endian, object format or layout digest mismatch. |
| `VAR-PROFILE-COPY` | A GC/sync/async family has a copied semantic body rather than a facade or justified provider. |
| `SOSIX-BYPASS` | New app/compiler/renderer host effect bypasses the approved service/provider boundary. |
| `SOSIX-BLOCKING` | Poll/pump/device call graph reaches a blocking host operation. |
| `SOSIX-RETIRE` | Reuse/unload before native work and retained consumer ownership retire. |
| `VAR-FAKE-EVIDENCE` | Declaration, source scan or emitted file promoted to executed/native/GPU evidence. |

Integrate these names into the existing diagnostics taxonomy during implementation; do not allocate a conflicting numeric range in this document.

### 12.3 Duplicate-code checks that do not punish legitimate ISA code

Use several levels rather than one unreliable “similarity score”:

**Always-on changed-file checks:** duplicate exact bodies after harmless formatting normalization; repeated registry/schema definitions; forbidden native imports; duplicated service IDs; new large facade bodies; manual edits to generated code; missing owner/retirement metadata.

**CI structural checks:** normalized AST fingerprints and import graph comparisons identify likely copies across library families, platforms and providers. Similarity alone is a review signal, not proof of semantic equivalence. Fail automatically when exact duplicate ownership, identical copied bodies or an explicit contract violation is established.

**Analysis checks:** broader clone detection and semantic/differential review distinguish a real target schedule from copied policy. A shared function specialized at compile time is preferable to copy/paste. A hand-tuned kernel is permitted with a named semantic owner, reason, independent oracle and performance evidence—not a blanket directory exemption.

No detector can prove that all semantic duplication is absent. The enforceable goal is **no new authoritative duplicates, no known unregistered copies, and measurable retirement of existing duplicates**. Architecture review remains necessary for cases that cannot be decided mechanically.

### 12.4 Ratchets and source-of-truth rules

Track the count of duplicate owners, concrete-provider imports from common modules, raw host-effect bypasses, live legacy routes, copied facade bodies and unqualified fallback claims. Establish a baseline without relabeling debt as resolved. New changes cannot increase it; owner-consolidation phases must reduce their assigned rows.

Generated tables must carry source/generator digests and reproducibility checks. A generated Rust/C/Simple ABI declaration is a projection, not an independently editable table. Native bridges can differ by language/runtime mechanics but cannot contain separate handwritten policy or lifecycle definitions.

### 12.5 Local and remote hooks remain bounded

Local pre-commit checks inspect changed imports, manifest/SDN shape, duplicate IDs, source links and generated-file status. Reuse cached dependency/AST summaries. Local pre-push runs affected conformance/alias/lifetime tests and verifies trace links; it does not boot the whole QEMU or GPU matrix.

Remote CI runs target-profile and provider contract matrices for impacted slots. Hardware/emulator jobs produce separate environment-bound receipts. Scheduled or explicit analysis builds run broad clone detection and expensive optimization/performance sweeps. Do not move correctness-critical admission validation into an optional heavy scan.

The build runner—not a mandatory test runner dependency—performs the compile and cache work. Tests, docs and TLDR freshness checks consume its results through the existing workflow.

### 12.6 Migration commits cannot leave two semantic owners

Prefer a move plus compatibility export, or redirect consumers to the existing owner. Separate move/rename commits from behavior changes for auditability. A temporary mirror requires an explicit immutable/generated status and removal gate; it is not a new implementation that agents may edit independently.

Old and new **bindings** can coexist for rollback, but only one is selected for a given session/slot. Two independently maintained operation state machines are not an acceptable rollback mechanism. Keep the old artifact when needed, not a permanent fork of its source semantics.

## 13. Nonbreaking implementation and retirement plan

### 13.1 Order and phase ownership

| Phase | Implementation work | Existing owner to extend | Required retirement / exit gate |
|---|---|---|---|
| **P0 — Evidence and owner census** | Merge prior SIMD audit with SOSIX route census; enumerate registries, selectors, Future families, native host effects and actual provider wiring. Capture fresh build/runtime baselines. | Existing feature/route records, SSpec and build runner | Each candidate has owner, source, callers and evidence level. No support promotion from a plan. |
| **P1 — Bind to existing environment contracts** | Normalize old feature/tier/options projections into `EnvironmentSnapshotV1` and `TargetCodegenProfileV1`; extend missing architecture/ABI IDs safely. | `composition/environment_variants`, canonical target registry | No new peer snapshot/selector schema. Old public types become views/facades; codec/validator parity passes. |
| **P2 — Isolate source and provider slots** | Add scoped applicability/ownership to relevant overlays; bridge legacy SIMD roots; generate a discoverable index. | Current module resolver + catalog metadata | One resolution decision; unrelated shadowing rejected; exact selected-source cache key verified. |
| **P3 — Complete SOSIX library/lifecycle wiring** | Reconcile Future/task wake and lifetime, host-service injection, error-domain adapters and existing sync/raw surfaces. Retire duplicate legacy semantic implementations. | Common SOSIX/execution contracts, async bridge, hosted SOSIX | Shared operation/lifetime tests, no spin/block in poll, retained buffers safe, no independent Future copy. |
| **P4 — Qualify native OS providers** | Wire existing Linux and non-Linux native implementations through reviewed runtime ABI/build lists; retain honest portable fallback. | Existing native OS provider owners below SOSIX | Source -> compile -> link -> bind -> execute receipts per OS; old bypass removed only after parity. |
| **P5 — Generalize existing SIMD planning** | Inject target profile; unify opcode legality; add precise requirement evidence; expand dynamic/tail/SLP/scalable support one transformation at a time. | Existing MIR optimizer, feature-capability seam and native encoders | Restricted Active path stays correct; differential tests pass; obsolete x86-host fallback logic retired. |
| **P6 — Qualify GPU runtime/compile facets** | Normalize CUDA/Metal/Vulkan API identity and artifact contracts; bind existing native providers to SOSIX lifecycle; share transfer/resource plan. | Portable-compute/ProcessingIR and existing GPU runtimes | Real per-backend compile/submit/complete/parity; no duplicated resource manager or scheduler. |
| **P7 — Advanced optimization** | Add opt-in GPU extraction, shared fusion/tiling/reduction and tuned SIMD choices, with budgeted analysis. | Shared analysis + target schedule providers | Measured end-to-end benefit, including transfers; strict numerical/effect rules unchanged. |
| **P8 — SimpleOS/direct transport and packaging** | Migrate admitted SimpleOS routes, native queues where qualified, multiversion/SMF packages and safe provider generations. | Existing SimpleOS ABI/provider, loader, binding runtime | Real trap/link/registration/live evidence; drain-before-unload; incompatible targets never fall back across ABI. |
| **P9 — Delete obsolete owners and close** | Remove redundant selectors, detectors, copied family bodies and stale routes; update docs/skills/TLDR. | Existing owners and trace DB | No remaining unregistered duplicates; zero broken links; all claimed rows backed by receipts. |

P4 and P5 can proceed independently after their contracts are frozen; GPU compile-only work can also proceed without native GPU hardware. Their release gates remain separate. Do not block a safe x86/SOSIX core improvement on an unimplemented DSP or native device-initiated I/O path, but leave that path explicitly unsupported.

### 13.2 Concrete source-route migration map

| Existing location / route | Change | Do not do |
|---|---|---|
| `compiler/30.types/simd_capabilities.spl` + Rust `simple-simd` | Preserve provider-specific probes; share registered feature meaning and normalize into the existing snapshot. Remove redundant decode/policy owners after parity. | Duplicate both into `compiler/target/probe` and `runtime/target/probe`. |
| `compiler/70.backend/feature_caps*.spl` | Keep target-legality/cost facade; receive canonical target-codegen input. | Add another all-ISA cost registry with different feature names. |
| `auto_vectorize_target.spl` | Replace host-global x86 selection with explicit target/profile input and legal shape choice. | Treat non-x86 absence of CPUID as an x86-v3 capability. |
| `auto_vectorize_receipt.spl` | Make requirement semantics target/ISA-aware, integrate typed driver failure and existing codegen receipt stages. | Satisfy AVX2/AVX-512 by width alone or treat log-only recognition as success. |
| Top-level `variants/` and Rust stdlib tier roots | Normalize legacy layout into the scoped current resolver; preserve aliases until callers migrate. | Keep two separate filesystem searches and different cache invalidation rules. |
| `nogc_sync_mut/simd/variant_dispatch.spl` | Adapt routing to an admitted binding/callable view; retain necessary public compatibility. | Add an independent dynamic SIMD registry beside the environment catalog. |
| `gpu_portable_compute.spl` and Vulkan route | Consolidate shared operation/layout/artifact metadata; keep distinct emitters. | Copy the full emitter once per API to resolve an enum mismatch. |
| Existing GPU runtime backends | Bind native runtime facets to shared SOSIX operation/resource semantics. | Create a new `sosix_cuda_runtime`, `sosix_metal_runtime` or renderer-private device manager. |
| `src/os/sosix/core/*` and common SOSIX contracts | Keep pure core in common; old names re-export; inspect and retire legacy I/O only with live parity. | Copy the core back into each OS provider. |
| `nogc_async_mut/async`, `async_host`, `src/future` families | One result/task contract, executor-side wake adapter, compatibility aliases. | Preserve unrelated Promise/Future lifecycles under family-specific names. |
| Compiler/interpreter/loader host-effect routes | Inject the same SOSIX services and preserve existing driver/loader policy contracts. | Mass-rename `rt_*` symbols and claim consolidation without route/lifetime proof. |

### 13.3 Phase deliverable contract

Each phase submits a small SDN/Markdown change record referencing the existing traceability database:

```sdn
migration:
  slot: existing_semantic_slot
  owner_before: existing_owner
  owner_after: same_or_relocated_owner
  aliases_retained: []
  duplicate_bodies_removed: []
  evidence_refs: []
  baseline_ref: recorded_before_change
  structural_budget: no_extra_hot_path_hop
  rollback: previous_admitted_binding
  status: proposed
```

Empty arrays here are illustrative fields, not a claim that the implementation has no debt. A real phase cannot close until its evidence and retirement rows are filled and verified.

### 13.4 Parallel-agent boundaries

One contract owner controls registry/schema/service-ID changes. Separate agents may handle source resolution, SIMD lowering, native OS providers, GPU compile/runtime adapters and verification. They consume frozen contracts and submit extension requests rather than introducing local substitutes.

Give each agent exact allowed files and semantic slots. A provider task cannot change common numerical semantics; a documentation task cannot change support flags; a SIMD task cannot add a private host probe. Shared contract changes land before dependent provider rewrites. Separate move-only changes from fixes and preserve rollback by artifact/binding generation.

## 14. Verification matrix

### 14.1 Required evidence levels

Record stages separately: **declared -> source accepted -> compiled -> linked/loaded -> bound -> executed -> semantically equivalent -> performance measured**. Not every consumer needs every stage, but a native/GPU support claim must identify which have actually been demonstrated. Reuse current environment and codegen receipt records, attaching SSpec/measurement references instead of creating another receipt ontology. [R02][R03]

| Category | Mandatory negative and positive cases |
|---|---|
| Isolation | Common imports a concrete provider; transitive vendor SDK leak; unknown owner; renderer overlay attempts filesystem override; duplicate registry definition. |
| x86 | SSE2 baseline; optional SSE subfeatures; AVX/AVX2 with missing OS state; AVX-512F without BW/DQ/VL/CD as appropriate; narrower EVEX vs 512-width requirements; policy downscope. |
| Arm | ARM32 with/without NEON, MVE profile isolation, AArch64 NEON, SVE/SVE2 with varied worker VL, streaming-mode boundary refusal, vendor-name-only feature claim rejected. |
| RISC-V | RV32/RV64 without vectors; RVV/Zve subsets; multiple VLEN/SEW/LMUL values; agnostic versus zero/merge tails; userspace vector permission; no privileged `misa` assumption. |
| 32/64 and ABI | Size/align/offset/argument/return canaries; overflowed address conversion; wrong endian/object format; scalar fallback still rejected on incompatible ABI. |
| SIMD semantics | Lengths 0 through several vector widths including every remainder; exact/disjoint/partial alias; unaligned data; masked guard-page tails; FP NaN/-0; overflow/trap ordering; duplicate scatter indexes. |
| SOSIX lifecycle | Queue full without hidden allocation; double completion; cancellation race; timeout before native retirement; out-of-order release; generation exhaustion; stale capability/token. |
| Async/sync/GC | Same operation outcome across facades; no new implementation body; paired Promise value/wake; sync-wait prohibition in poll/pump; bounded profiles enforced. |
| POSIX/raw | Native error domain retained; raw negative errno distinct from POSIX; partial read/write; zero-length contract; `O_APPEND` positioned behavior handled explicitly. |
| GPU | CUDA/Metal/Vulkan artifact acceptance, actual launch, completion and numeric comparison; unsupported type/feature; barrier/subgroup variation; device loss; no false GPU receipt on CPU fallback. |
| Host/device boundary | Raw host pointer rejected; stale resource generation; bounds/permission failure; rejected service cannot trigger host work; direct-transport claims require proof. |
| Loader / reload | Incompatible/untrusted artifact rejected before executable entry; no bootstrap cycle; session pins old generation; unload waits for callbacks and leases. |
| Build/cache | Strong build host cross-compiles weaker/different target; static `@when` alters imports correctly; relevant-only invalidation; source parse cache reused; legacy resolver agrees. |
| SimpleOS | Correct trap entry, linked strong symbol, provider registration, live completion/serial behavior, freestanding import closure, kernel SIMD context policy. |
| Performance | Cold/warm build, RSS, resolver probe count, dispatch/hops/copies, end-to-end GPU thresholds, code-size growth, AVX2 versus AVX-512 per qualified workload. |

### 14.2 Differential test design

Use identical input cases and contracts for scalar, SIMD and GPU implementations. Compare bit-for-bit for exact contracts; use specified tolerance only for an explicitly relaxed contract. Do not hide NaNs, signed zero, overflow or ordering differences in a blanket floating-point epsilon.

Test not only final arrays but side effects, return errors, buffer liveness and which implementation ran. A disassembly test proves an instruction was emitted, not that execution reached it. Runtime provider counters or an instruction/device trace must be tied to the exact artifact and input. Full tracing belongs in test/diagnostic builds; production may retain only bounded receipt identity.

### 14.3 What emulation does and does not prove

QEMU and software GPU implementations can qualify behavior for their recorded configuration. They do not prove physical GPU performance, PCIe coherence, native device-initiated doorbells or hardware-specific context behavior. Maintain separate emulator and hardware rows. An unavailable target produces an explicit skip/blocker, never a passing placeholder.

Reuse existing `test/01_unit/os/sosix`, `test/02_integration/os/sosix`, common contract specs and compiler/GPU test families; add cases to those owners instead of copying a complete new test hierarchy. Keep an independent oracle where shared production code would mask the same defect.

## 15. Worked composition examples

### 15.1 One bitmap operation across x86 OS variants

The portable bitmap contract and body are authored once. The x86 vector provider supplies SSE2/AVX2/AVX-512 schedules and exact feature predicates; the same semantic tests apply. Linux and Windows differ in callable ABI or native loading, not in the bitmap algorithm.

A static application calls its selected kernel directly. A multiversion package binds an admitted function once at a suitable boundary. A dynamic package uses SOSIX only to perform native library mechanisms and environment setup, while loader policy admits the artifact. None of these choices adds a SOSIX operation for each bitmap AND.

**Expected edit for a new OS:** native loader/probe/ABI adapter and registration where required; zero copied bitmap or vectorizer bodies.

### 15.2 Qualcomm CPU, Adreno GPU and Hexagon

The CPU path uses its registered Arm ISA features. An available Adreno API is a separate GPU device session. HVX is an optional Hexagon-domain provider, not an ARM feature bit. The portable operation contract and shared candidate analysis remain common; each admitted domain chooses a different schedule/artifact. [E07]

The OS provider supplies services and device access. Do not create a `qualcomm_sosix` variant for all algorithms or assume all Qualcomm parts expose identical accelerators. Lack of a qualified DSP runtime leaves HVX unavailable while CPU/GPU paths can remain usable.

### 15.3 AArch64 cross-build on an AVX-512 workstation

The compiler itself may tokenize using a host AVX-512 provider. Output `TargetCodegenProfileV1` is AArch64 with its selected ABI/ISA and does not inherit host CPUID. The parser result can be reused because its semantics are unchanged; target-dependent type/layout/lowering caches are separate.

A Metal kernel artifact can be planned without loading a Metal device into the build-host process, subject to the available toolchain. Execution qualification runs on the actual target. Host compilation speed and output ISA are independent bindings, not one global `simd_tier`.

### 15.4 One file-to-GPU pipeline

A caller requests a positioned file read through canonical SOSIX. The selected OS provider completes the read and retires its native access. The shared execution planner then schedules a buffer transfer or admitted shared-memory transition and launches the generated CUDA/Metal/Vulkan kernel. The GPU provider reports completion through the same task/lifetime vocabulary.

A timeout does not free either the native I/O buffer or GPU resource prematurely. The renderer/tensor library owns the operation semantics; SOSIX owns service and lease transitions; the native adapter owns API mechanics. There is no file-to-CUDA-specific Future or one copy of the file reader per GPU API.

### 15.5 RV32 mission-pool SimpleOS

The target declares a 32-bit ABI, allowed scalar/vector subset and no-GC fixed-capacity profile. Shared range/layout code specializes for its widths. The SimpleOS provider binds common SOSIX contracts to existing kernel operations. No host libc, desktop executor or GPU SDK enters its import closure.

If vector context support or a requested 64-bit atomic is unavailable, the precise operation chooses an admitted primitive or refuses. The profile does not manufacture support by copying RV64 code into a `bits32` directory. Pool exhaustion is a typed admission failure before unsafe submission.

### 15.6 Adding a new SIMD extension

Add feature/dependency rows to the existing registry, a native lowering/cost descriptor and a qualified probe projection when needed. Extend tests for capability refusal, emitted instruction and scalar parity. The shared vectorizer consumes the descriptor; applications and SOSIX do not change.

Only a genuine new algorithmic scheduling primitive warrants a shared optimizer change. A new instruction name is not a reason for `auto_vectorize_avx_new.spl` to duplicate the coordinator, alias checks or CFG rewriting.

## 16. Documentation, Spipe and traceability

### 16.1 Update existing documents rather than adding competing plans

| Existing document / area | Required update |
|---|---|
| `doc/04_architecture/compiler/simd/simd_unified_architecture.md` | Precise fixed/scalable/SIMT distinction, explicit inactive-lane semantics, exact ISA versus width requirements, canonical ownership links. |
| `doc/04_architecture/runtime/host_cpu_runtime_variants.md` | Existing environment catalog/binding integration; process versus worker/device state; implemented artifact versus detected capability. |
| `doc/05_design/runtime/sosix_runtime_unification_design.md` | Cross-reference the final variation boundaries; preserve SOSIX operation and SimpleRing authority; include GPU lease/retirement and no-second-runtime rules. |
| `doc/01_research/local/sosix_runtime_unification.md` and route manifests | Add actual retirement and production-wiring evidence; retain dated historical findings and supersession notes. |
| `doc/07_guide/lib/sosix_runtime_library.md` | Reconcile conflicting availability sections and exact POSIX terminology from current source-matched execution. |
| Processing backend architecture/guide | Shared planner plus separately qualified backend compile/runtime facets; no duplicate scheduler or resource owner. |
| `variants/FILE.md`, manifest and resolver plan | Sparse owned-slot policy; generated index; no generic copied bitness families; preserve bootstrap-safe parsing. |
| Old SIMD analysis-only/skeleton records | Mark superseded status with current source/evidence, without deleting historical failure analysis. |

Do not overwrite a historical report's claims with a new date and pretend the old tests ran on the new source. Link the new evidence explicitly.

### 16.2 Spipe guidance

Reuse the existing SOSIX feature expert and register missing routing through the current knowledge registry. Add variation guidance under the existing compiler/runtime feature routes, not a separate unconnected wiki. Keep common policy in one owner and use pointers from project skills. No company/private namespace is presumed by this report. [R05][R11]

The agent workflow must first identify the semantic owner and existing provider/contract, then name the exact differing primitive. Before proposing a file, it must state which current body will be reused, moved or retired. It must not duplicate a schema, Future, feature decoder, service table or backend-selection ladder to avoid coordinating with another agent.

For every claimed support change, the skill asks for exact target/profile, artifact digest, bound provider generation, evidence stage and SSpec/benchmark reference. A source scan, passing model fixture or generated shader is never described as native execution.

### 16.3 Traceability and TLDR

Use the existing SDN trace database: requirement -> feature -> acceptance SSpec -> unit/integration/system tests -> source owner -> implementation/provider -> receipt. Add variation axes as attributes, not separate copies of the feature row for every OS/ISA permutation.

TLDR summaries record stable module names, allowed static conditions and the owner link. IDE/Spipe source changes feed the already planned edit/dependency metadata; this design does not introduce another timestamp authority. Mark generated documentation and update summaries only from source/evidence changes that affect them.

## 17. Completion criteria

The integrated migration is complete only when each claimed scope meets all of the following:

1. **Ownership:** every semantic slot, feature/service ID and lifecycle has one authority; no new independent copy or unregistered provider exists.
2. **Isolation:** common algorithms do not import concrete OS/ISA/GPU implementations; the compiler/runtime/kernel dependency directions pass resolved-graph checks.
3. **Existing infrastructure:** environment snapshots, codegen profiles, catalog/admission/bindings, SOSIX and SimpleRing are reused rather than reimplemented under new names.
4. **Correct targeting:** output target, runtime process, worker vector state and device generation are distinguished; ABI/32/64/endian incompatibility fails closed.
5. **Behavior:** admitted SIMD/GPU variants preserve the chosen semantic/numerical/effect contract; impossible hard requirements fail visibly.
6. **Async safety:** one operation/result lifecycle; no blocking poll; timeout/cancel does not release still-live buffers; provider unload waits for retirement.
7. **Performance:** ordinary SIMD stays direct; native service consolidation adds no unjustified hop/copy; caches share only valid common work; measured regressions are resolved or explicitly accepted.
8. **Evidence and retirement:** actual production paths are tested at their claimed level, old owners are removed or reduced to bounded compatibility facades, and docs/traceability reflect the result.

**Final architecture:** one semantic compiler and library foundation; the existing environment-variant authority for target/capability/binding decisions; sparse `variants/` source seams; isolated ISA/ABI/OS/GPU providers; and one SOSIX/SimpleRing service lifecycle. New targets add qualified differences—not another copy of Simple.

## 18. Sources

### 18.1 Repository evidence

All repository links below are pinned to `a9777ac75fa5d64c6741de8981a9d13815990179`. R01–R06 and the environment exports/codegen contract were directly fetched in this revision. SIMD/variant implementation paths also draw on the preceding conversation audit. R09 was additionally read through its source-contract, wire-ABI, tier, compiler-checking and migration sections. R07, R08, R10 and R11 are linked authorities or discovery results identified through the inspected SOSIX sources; these links are not a claim that their complete implementations were independently executed or exhaustively audited here.

- **R01 — Environment boundary records and validators:** `src/lib/nogc_sync_mut/composition/environment_variants/contracts_v1.spl`. [R01]
- **R02 — Existing catalog, policy, admission, binding and receipt exports:** `src/lib/nogc_sync_mut/composition/environment_variants/__init__.spl`. [R02]
- **R03 — Host/target-separated codegen evidence contract:** `src/lib/nogc_sync_mut/composition/environment_variants/target_codegen_profile_v1.spl`. [R03]
- **R04 — SOSIX consolidation design, with later alias candidate addendum:** `doc/05_design/runtime/sosix_runtime_unification_design.md`. [R04]
- **R05 — SOSIX local evidence, dated September 26 and September 28:** `doc/01_research/local/sosix_runtime_unification.md`. [R05]
- **R06 — SOSIX runtime guide, including dated provider limitations:** `doc/07_guide/lib/sosix_runtime_library.md`. [R06]
- **R07 — Existing SimpleRing/task contract (identified in the SOSIX design):** `src/lib/common/contracts/execution/simple_ring_async_v1.spl`. [R07]
- **R08 — SOSIX blocked rows and resume conditions:** `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md`. [R08]
- **R09 — SOSIX-G checked profile, transport tiers, wire contracts and migration plan:** `doc/01_research/local/sosix_gpu_api_extension_final_report.md`. [R09]
- **R10 — Existing rendering-host boundary authority (referenced by SOSIX design):** `doc/01_research/local/sosix_wm_renderer_host_interface.md`. [R10]
- **R11 — Existing SOSIX feature expert route:** `doc/00_llm_process/feature_expert/sosix_runtime_unification/skill.md`. [R11]
- **R13 — Existing variants manifest:** `variants/__init__.spl`. [R13]
- **R14 — Existing project variation configuration:** `config/var.sdn`. [R14]
- **R15 — Self-hosted variation resolver:** `src/compiler/99.loader/module_resolver/var_resolution.spl`. [R15]
- **R16 — Legacy SIMD-tier stdlib root projection:** `src/compiler_rust/compiler/src/stdlib_variant.rs`. [R16]
- **R17 — Canonical target registry owner:** `src/compiler/80.driver/canonical_target_registry_owner_v1.spl`. [R17]
- **R18 — SIMD capability detector:** `src/compiler/30.types/simd_capabilities.spl`. [R18]
- **R19 — Target feature/cost facade:** `src/compiler/70.backend/feature_caps.spl`. [R19]
- **R20 — MIR optimizer pass status and wiring:** `src/compiler/60.mir_opt/mir_opt/mod.spl`. [R20]
- **R21 — SIMD requirement evidence and current width-based checks:** `src/compiler/60.mir_opt/mir_opt/auto_vectorize_receipt.spl`. [R21]
- **R22 — Current auto-vectorization target resolver:** `src/compiler/60.mir_opt/mir_opt/auto_vectorize_target.spl`. [R22]
- **R23 — Portable GPU emission and artifact contract:** `src/compiler/70.backend/backend/gpu_portable_compute.spl`. [R23]
- **R24 — GPU target aliases and backend-order metadata:** `src/compiler/00.common/gpu_target_metadata.spl`. [R24]
- **R25 — Processing backend guide and partial-scope status:** `doc/07_guide/compiler/backends/processing_backend.md`. [R25]
- **R26 — Current vectorization rewriter:** `src/compiler/60.mir_opt/mir_opt/_AutoVectorize/rewrite.spl`. [R26]
- **R27 — Existing unified fixed/scalable SIMD architecture:** `doc/04_architecture/compiler/simd/simd_unified_architecture.md`. [R27]
- **R28 — Current runtime SIMD routing facade:** `src/lib/nogc_sync_mut/simd/variant_dispatch.spl`. [R28]
- **R29 — Existing target presets:** `src/compiler/70.backend/target_presets.spl`. [R29]
- **R30 — Existing session-time codegen factory:** `src/compiler/70.backend/backend/codegen_factory.spl`. [R30]

### 18.2 Primary external documentation

External documentation was checked on 2026-10-10. It supports the API/ISA constraints, not the implementation readiness of Simple. Living documentation may change; implementation receipts should record the toolchain and specification revision used.

- **E01 — GCC x86 options: ISA selection, tuning and feature families.** [E01]
- **E02 — Arm C Language Extensions: NEON, SVE, SME and MVE.** [E02]
- **E03 — Linux AArch64 SVE state and vector-length contract.** [E03]
- **E04 — Linux RISC-V vector enablement interface.** [E04]
- **E05 — Linux x86 XSTATE authorization, including dynamic state.** [E05]
- **E06 — RISC-V V extension 1.0, ratified ISA library revision 20260120.** [E06]
- **E07 — Qualcomm Hexagon DSP and HVX architecture.** [E07]
- **E08 — LLVM loop and SLP auto-vectorization.** [E08]
- **E09 — Linux io_uring cancellation documentation.** [E09]
- **E10 — Vulkan synchronization and cache-control specification.** [E10]
- **E11 — CUDA asynchronous execution guide.** [E11]
- **E12 — Linux pread/pwrite semantics, errors and O_APPEND caveat.** [E12]
- **E13 — CUDA SIMT, synchronization scopes and collision semantics.** [E13]
- **E14 — Vulkan subgroup capabilities and size variability.** [E14]
- **E15 — CUDA stream-ordered allocation and lifetime ordering.** [E15]
- **E16 — Metal compute-pipeline thread execution width.** [E16]

### 18.3 Verification limits

This revision inspected source and documents through the repository connection and read the full preceding Markdown report. It did not run Simple, rebuild runtime artifacts, exercise a native OS/GPU provider, execute QEMU, inspect the entire repository import graph, or measure performance. Therefore “must,” “proposed,” and phase gates are requirements, not completed work. Where documents disagree, this plan preserves the discrepancy and requires source-matched execution evidence before making a support claim.

[R01]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/src/lib/nogc_sync_mut/composition/environment_variants/contracts_v1.spl "Environment boundary records and validators"
[R02]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/src/lib/nogc_sync_mut/composition/environment_variants/__init__.spl "Existing catalog, policy, admission, binding and receipt exports"
[R03]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/src/lib/nogc_sync_mut/composition/environment_variants/target_codegen_profile_v1.spl "Host/target-separated codegen evidence contract"
[R04]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/doc/05_design/runtime/sosix_runtime_unification_design.md "SOSIX consolidation design, with later alias candidate addendum"
[R05]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/doc/01_research/local/sosix_runtime_unification.md "SOSIX local evidence, dated September 26 and September 28"
[R06]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/doc/07_guide/lib/sosix_runtime_library.md "SOSIX runtime guide, including dated provider limitations"
[R07]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/src/lib/common/contracts/execution/simple_ring_async_v1.spl "Existing SimpleRing/task contract (identified in the SOSIX design)"
[R08]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md "SOSIX blocked rows and resume conditions"
[R09]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/doc/01_research/local/sosix_gpu_api_extension_final_report.md "SOSIX-G checked profile, transport tiers, wire contracts and implementation plan"
[R10]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/doc/01_research/local/sosix_wm_renderer_host_interface.md "Existing rendering-host boundary authority (referenced by SOSIX design)"
[R11]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/doc/00_llm_process/feature_expert/sosix_runtime_unification/skill.md "Existing SOSIX feature expert route"
[R13]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/variants/__init__.spl "Existing variants manifest"
[R14]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/config/var.sdn "Existing project variation configuration"
[R15]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/src/compiler/99.loader/module_resolver/var_resolution.spl "Self-hosted variation resolver"
[R16]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/src/compiler_rust/compiler/src/stdlib_variant.rs "Legacy SIMD-tier stdlib root projection"
[R17]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/src/compiler/80.driver/canonical_target_registry_owner_v1.spl "Canonical target registry owner"
[R18]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/src/compiler/30.types/simd_capabilities.spl "SIMD capability detector"
[R19]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/src/compiler/70.backend/feature_caps.spl "Target feature/cost facade"
[R20]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/src/compiler/60.mir_opt/mir_opt/mod.spl "MIR optimizer pass status and wiring"
[R21]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/src/compiler/60.mir_opt/mir_opt/auto_vectorize_receipt.spl "SIMD requirement evidence and current width-based checks"
[R22]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/src/compiler/60.mir_opt/mir_opt/auto_vectorize_target.spl "Current auto-vectorization target resolver"
[R23]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/src/compiler/70.backend/backend/gpu_portable_compute.spl "Portable GPU emission and artifact contract"
[R24]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/src/compiler/00.common/gpu_target_metadata.spl "GPU target aliases and backend-order metadata"
[R25]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/doc/07_guide/compiler/backends/processing_backend.md "Processing backend guide and partial-scope status"
[R26]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/src/compiler/60.mir_opt/mir_opt/_AutoVectorize/rewrite.spl "Current vectorization rewriter"
[R27]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/doc/04_architecture/compiler/simd/simd_unified_architecture.md "Existing unified fixed/scalable SIMD architecture"
[R28]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/src/lib/nogc_sync_mut/simd/variant_dispatch.spl "Current runtime SIMD routing facade"
[R29]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/src/compiler/70.backend/target_presets.spl "Existing target presets"
[R30]: https://github.com/ormastes/simple/blob/a9777ac75fa5d64c6741de8981a9d13815990179/src/compiler/70.backend/backend/codegen_factory.spl "Existing session-time codegen factory"
[E01]: https://gcc.gnu.org/onlinedocs/gcc/x86-Options.html "GCC x86 options: ISA selection, tuning and feature families"
[E02]: https://arm-software.github.io/acle/main/acle.html "Arm C Language Extensions: NEON, SVE, SME and MVE"
[E03]: https://docs.kernel.org/arch/arm64/sve.html "Linux AArch64 SVE state and vector-length contract"
[E04]: https://docs.kernel.org/arch/riscv/vector.html "Linux RISC-V vector enablement interface"
[E05]: https://docs.kernel.org/arch/x86/xstate.html "Linux x86 XSTATE authorization, including dynamic state"
[E06]: https://docs.riscv.org/reference/isa/v20260120/unpriv/v-st-ext.html "RISC-V V extension 1.0, ratified ISA library revision 20260120"
[E07]: https://docs.qualcomm.com/bundle/publicresource/topics/80-78185-2/dsp.html?product=1601111740035277 "Qualcomm Hexagon DSP and HVX architecture"
[E08]: https://llvm.org/docs/Vectorizers.html "LLVM loop and SLP auto-vectorization"
[E09]: https://man7.org/linux/man-pages/man7/io_uring_cancelation.7.html "Linux io_uring cancellation documentation"
[E10]: https://docs.vulkan.org/spec/latest/chapters/synchronization.html "Vulkan synchronization and cache-control specification"
[E11]: https://docs.nvidia.com/cuda/cuda-programming-guide/02-basics/asynchronous-execution.html "CUDA asynchronous execution guide"
[E12]: https://man7.org/linux/man-pages/man2/pread.2.html "Linux pread/pwrite semantics, errors and O_APPEND caveat"
[E13]: https://docs.nvidia.com/cuda/cuda-programming-guide/03-advanced/advanced-kernel-programming.html "CUDA SIMT, synchronization scopes and collision semantics"
[E14]: https://docs.vulkan.org/guide/latest/subgroups.html "Vulkan subgroup capabilities and size variability"
[E15]: https://developer.nvidia.com/blog/using-cuda-stream-ordered-memory-allocator-part-2/ "CUDA stream-ordered allocation and lifetime ordering"

[E16]: https://developer.apple.com/documentation/metal/mtlcomputepipelinestate/threadexecutionwidth "Metal compute-pipeline thread execution width"
