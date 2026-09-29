<!-- codex-research -->

# Simple SOSIX-G

## Compile-Time API Extension, CUDA Device Access, Frozen Interfaces, and Parallel Implementation Plan

**Date:** 2026-08-11  
**Repository audited:** `ormastes/simple`  
**Audit revision:** `289ff0f35200d41f3368daccdea4b1334a38b52b`  
**Status:** Final research, architecture, design, migration, and parallel-agent execution report  
**Repository changes made by this report:** None

## 1. Executive decision

Simple should support CUDA device code calling a restricted, asynchronous SOSIX API. The feature should be named **SOSIX-G** and implemented as a checked execution profile, not as unrestricted POSIX inside CUDA.

```text
Simple/CUDA device function
        |
        | typed SOSIX-G call
        v
GPU-callable device library
        |
        | system-scope submission ring
        v
SOSIX GPU proxy process
        |
        +--> normal SOSIX VFS/network/IPC/device services
        |
        +--> optional direct-data backend
             - GPUDirect Storage
             - RDMA / NVSHMEM / IBGDA
             - future native device-initiated NVMe
        |
        v
GPU-visible completion ring
```

The compiler must distinguish four guarantees:

1. Type and extension correctness.
2. Transitive GPU execution legality.
3. Explicit SOSIX API availability as GPU-local, GPU-proxied, or host-only.
4. Deployment availability of the ABI, transport, coherence, and optional direct-data capabilities.

`extend TypeName:` alone does not provide those guarantees. It is currently an ergonomic feature rather than a robust compile-time API-contract mechanism. SOSIX-G should combine checked traits and impls, hardened extension methods, compiler-owned `@sosix_api` metadata, whole-call-graph GPU legality, backend ABI manifest validation, and runtime capability validation. It should not depend on proposed typed AOP facets.

## 2. Current extension and GPU support

### 2.1 Extension syntax exists but enforcement is incomplete

The Rust seed parses `extend TypeName:` into an `ExtendBlock` containing a target type, generic parameters, and methods. The self-hosted parser also has an extension/impl path.

The Rust-seed checker, however, treats `Node::Extend` as introducing no type in its first pass and has no dedicated second-pass validation arm. There is no extension coherence table equivalent to trait-impl coherence, and unexpected non-function content in an extension body is skipped rather than rejected.

Current `extend` therefore does not prove that the target exists, bind `self` to it, fully check bodies and effects, reject inherent conflicts or imported ambiguity, enforce stable visibility, or prevent execution-domain escalation.

Traits and checked impls are the strongest existing static foundation. Phase 1 should expose canonical traits/functions and checked impl blocks. Phase 2 may add forwarding extension wrappers after extension hardening.

### 2.2 Other existing mechanisms

`bind Interface = Implementation` helps statically select a backend but does not prove API completeness, ABI compatibility, deployment capability, or device legality. Backend selection and conformance remain separate checks.

The self-host compiler's decorator-to-registry-to-semantic-pass pattern is suitable for SOSIX-G. GPU metadata already reaches HIR/MIR, but the current GPU checker is not invoked as a whole-program transitive walk. That is the principal compile-time fail-open.

SOSIX-G v1 must compile with the deployed Rust seed and use ordinary classes/newtypes/traits with private handles. Native affine `resource` types can follow only after self-host deployment and ownership enforcement are proven across all modes.

## 3. Domain conclusions

Prior systems establish feasibility: GPUfs exposed GPU file access; GPUnet exposed socket-like networking; BaM showed the need for high-throughput queues and request coalescing; GeminiFS uses a GPU-friendly companion filesystem and cache; NVSHMEM supports GPU-initiated communication on supported systems.

CUDA system-scope synchronization can coordinate CPU and GPU threads when the memory type and device capabilities permit it. Device-launchable graphs are host-instantiated, fixed, and restricted. GPUDirect Storage can DMA between storage and GPU memory, but cuFile calls remain CPU-issued.

SOSIX-G must therefore distinguish request initiation, data-transfer path, and control-plane execution. A CUDA kernel may enqueue an operation while the CPU proxy executes its control plane and the payload optionally follows a direct device path.

## 4. Normative architecture and tiers

There is one semantic SOSIX operation model shared by CPU async APIs, CUDA device APIs, and synchronous adapters. The device API is a restricted projection rather than a second OS API.

- **G0 GPU-local:** completion polling, timestamp, bounded trace/input rings, fixed-pool allocation, queue/event operations.
- **G1 host-proxied:** pre-authorized file I/O, pre-opened socket I/O, IPC queues, handle metadata, cancellation, and later authorized USB transfers.
- **G2 direct-data/device-initiated:** GDS, RDMA/NVSHMEM/IBGDA, and future GPU-owned NVMe queues.

G2 must never silently degrade to G1 or staged copying when the execution profile forbids fallback.

## 5. Frozen source contract

```simple
@sosix_api(
    id: 257,
    version: 1,
    domains: "host|gpu",
    gpu_transport: "host_proxy_ring",
    effects: "fs|async",
    backend_caps: "gpu_sosix_ring|gpu_system_atomics",
    flags: "cancellable|batchable|partial_progress|registered_buffer"
)
fn sosix_fs_read_at_async(
    file: GpuFileRead,
    dst: GpuWriteBuffer,
    file_offset: u64,
    length: u64,
    deadline: Deadline
) -> GpuOperation<ByteCount>
```

The v1 keys are exactly `id`, `version`, `domains`, `gpu_transport`, `effects`, `backend_caps`, and `flags`. Unknown or duplicate keys, unknown values, and invalid placement are compile errors.

Frozen flags are `async_only`, `cancellable`, `batchable`, `partial_progress`, `registered_buffer`, `control_plane`, `direct_data_optional`, `direct_data_required`, and `experimental`.

Frozen deployment capabilities are `gpu_sosix_ring`, `gpu_system_atomics`, `gpu_mapped_host_memory`, `gpu_device_graph`, `gpu_gds`, `gpu_rdma`, `gpu_device_initiated_storage`, and `gpu_proxy_reset`.

Deployment capabilities and per-resource rights remain separate. Initial wrappers include `GpuFileRead`, `GpuFileWrite`, `GpuReadBuffer`, and `GpuWriteBuffer`, each holding a private capability or buffer reference.

The canonical semantic API is a trait/function. An extension is only a checked forwarding façade and receives no special trust.

## 6. Compile-time semantic model

Every resolved function receives `FunctionExecutionSummaryV1`, including domains, effects, backend capabilities, resource rights, allocation/blocking/suspension/dynamic-dispatch/recursion facts, unresolved calls, and required SOSIX API IDs.

After module merge and type resolution, the compiler builds a graph by resolved symbol identity, collapses strongly connected components, seeds local facts, propagates summaries to a fixed point, and validates every GPU root. It retains predecessor edges so diagnostics include a concrete root-to-violation call path.

Sealed finite dispatch checks every target. Static bindings check the selected implementation and manifest. Compiler-known finite function-pointer sets check all targets. Open dispatch and unknown externs are rejected in v1.

Required diagnostics range from `E-SGX-001` through `E-SGX-015`, covering malformed contracts, host-only reachability, missing rights, invalid buffers, blocking calls, transitive paths, open dispatch, manifest/capability/fallback failures, extension errors, ABI/hash mismatch, and experimental opt-in.

One shared `validate_execution_contracts(module, target, profile)` gate must run for check, interpreter, JIT, AOT/native, SMF, cross-compilation, package/build graphs, and LSP incremental checking.

## 7. Required `extend` hardening

The parser must reject non-method declarations; consistently support decorators, visibility, async, static, and mutable receivers; preserve spans and attributes; reject fields/nested types; and parse generic targets through the normal type parser.

The checker must resolve the target, bind `self`, validate signatures/contracts/bodies/effects, reject inherent conflicts, reject duplicate or ambiguous visible extensions, validate generic constraints, and register a stable signature hash.

Frozen visibility:

- Same-capsule extensions are visible to the declaring module and descendants.
- Cross-capsule/package extensions require explicit `use`.
- Foreign extensions never enter the global prelude automatically.
- Mission-critical mode rejects wildcard-imported extensions.
- Resolution never depends on filesystem traversal or import order.

```text
inherent method
    >
explicit trait method
    >
exactly one visible extension method
```

More than one matching extension is a compile error.

## 8. Frozen SOSIX-G wire ABI v1

The ABI is little-endian and fixed-width. Requests contain no raw pointers. Resources and buffers use `(slot, generation)` references. Unknown flags are rejected; reserved fields are zero on send and ignored on compatible receive; breaking layout/semantics require major v2. Queue reset increments an epoch, and completions match request sequence, epoch, and user tag.

### 8.1 Layouts

`SosixGpuRingControlV1` is 256 bytes aligned to 128, with header/feature data, separated producer and consumer cache regions, doorbell, fault, reset generation, and reserved expansion space.

`SosixGpuRequestV1` is 128 bytes aligned to 64, containing sequence, API ID, flags, capability and buffer refs, offsets, length, deadline, completion/client/lane/QoS fields, cancellation token, three generic arguments, trace/user tags, checksum, and reserved space.

`SosixGpuCompletionV1` is 64 bytes aligned to 64, containing sequence, request sequence, user tag, status, flags, transferred bytes, auxiliary result, timestamp, reset generation, and checksum.

References encode table slot in bits 0..31 and generation in bits 32..63. CPU-owned 64-byte capability entries hold object ID, generation, kind, flags, rights, backend cookie, namespace, owner, audit label hash, and reserved data. The device sees the table read-only.

### 8.2 Queue protocol

Use a bounded per-slot sequence protocol: claim a position, wait for slot ownership, write fields, publish with system-scope release, consume with system-scope acquire, validate/execute, publish completion, then return the request slot by advancing its sequence by capacity. This prevents wraparound ABA.

`host_proxy_ring` is enabled only after a runtime probe proves valid CPU/GPU synchronization for the selected mapped memory. A failed probe disables the profile.

## 9. Device API and waiting policy

```simple
fn sosix_g_submit(request: GpuRequest) -> Result<GpuOperationId, GpuSubmitError>
fn sosix_g_poll(op: GpuOperationId) -> Option<GpuCompletion>
fn sosix_g_take_batch(out: GpuCompletionSlice) -> u32
fn sosix_g_cancel(op: GpuOperationId) -> CancelRequestResult
```

Device code has no ordinary blocking API implemented by unbounded spinning. Allowed strategies are nonblocking poll, explicitly bounded cooperative polling, kernel termination plus host continuation, a pre-instantiated device graph continuation, or a persistent-kernel scheduler with reserved occupancy and bounded waits.

One request per CUDA lane is prohibited by default. The API must offer warp/block coalescing, scatter/gather, and batch submission.

## 10. Frozen v1 registry

| ID | Operation | Tier |
|---:|---|---|
| `0x0001` | `TRACE_WRITE` | G0/G1 |
| `0x0002` | `CANCEL` | G1 |
| `0x0003` | `HEALTH_PING` | G1 |
| `0x0101` | `FS_READ_AT` | G1; optional G2 |
| `0x0102` | `FS_WRITE_AT` | G1; optional G2 |
| `0x0103` | `FS_STAT_HANDLE` | G1 control plane |
| `0x0201` | `NET_SEND` | G1; optional G2 |
| `0x0202` | `NET_RECV` | G1; optional G2 |
| `0x0203` | `NET_SEND_TO` | G1; optional G2 |
| `0x0204` | `NET_RECV_FROM` | G1; optional G2 |
| `0x0301` | `IPC_QUEUE_SEND` | G1 |
| `0x0302` | `IPC_QUEUE_RECV` | G1 |

USB, process control, and path-based namespace operations remain outside v1.

Supported v1 facilities are pre-opened file I/O, handle metadata, pre-opened socket I/O, mapped input and trace rings, and optional direct GDS/RDMA paths. DNS, socket creation, arbitrary path open, and administrative control stay host-side.

`fork`, pthreads, POSIX signal delivery into lanes, arbitrary `mmap`/`mprotect`, mount/setuid/driver loading, generic `ioctl`, and device-side `dlopen` are unsupported.

## 11. Backend manifest and profile reuse

Each backend emits `SosixGpuBackendManifestV1` with ABI version, contract hash, identity/build/target data, supported API IDs and capability bits, ring limits, inflight/payload limits, memory/direct-data modes, cancellation, and reset support.

At link/package time, required API and capability sets must be subsets of the backend manifest. At deployment, negotiation repeats against the actual device/driver.

Reuse existing `CpuReference`, `HybridVectorGpu`, `ResidentGpu`, `StageFallbackPolicy`, and `StorageCapabilityTier` vocabulary. Add only:

```text
GpuIoPreference
    Proxy
    DirectPreferred
    DirectRequired
    DeviceInitiatedRequired
```

GDS does not satisfy `DeviceInitiatedRequired`, because cuFile is CPU-issued. Every selection produces a receipt with requested/selected mode, transport, fallback reason, contract hash, backend build ID, hardware digest, and direct/staged byte totals.

## 12. SOSIX refactoring

The current implementation has two separate fixed 128-slot request tables, raw IDs/results, raw-FD backend routing, a nominally async read that immediately blocks on IPC receive, fixed reply-buffer copying, and busy-spinning sync wrappers.

Target ownership:

```text
src/os/sosix/
    core/       operation, completion, queue, cancellation, deadline, wait set, refs
    fs/         file and read/write
    net/
    ipc/
    input/
    usb/
    compat/     sync and POSIX FD adapters
    gpu/        contract and client
```

Migration adds the canonical operation core, capability-based VFS I/O, notification-based CPU waiting, robust sync wrappers, POSIX adapters preserving offsets/errno, and GPU proxy transport. It then deletes duplicate arrays, confines raw FDs to compatibility ownership, adds remaining domains, and generates façades from the frozen contract.

## 13. Parallel implementation plan

### 13.1 Serial contract freeze

The integration owner first lands the architecture document, canonical SDN schema and API IDs, shared compiler contract definitions, generated C/CUDA/layout artifacts, and one shared SHA-256 contract hash. Frozen files remain single-owner; CI rejects drift; shared parser/driver choke points also remain single-owner.

### 13.2 Parallel wave 1

- **WP-A:** Rust-seed extension hardening and coherence tests.
- **WP-B:** Rust-seed SOSIX-G typed call-graph/SCC checker.
- **WP-C:** self-host registry/checker diagnostic parity.
- **WP-D:** ABI generator and compatibility checker.
- **WP-E:** executable ring model and Lean proofs.
- **WP-F:** backend manifest/link validator and fallback receipts.

### 13.3 Parallel wave 2

- **WP-G:** CUDA device submission/completion client and coalescing.
- **WP-H:** validating SOSIX GPU proxy, recovery, audit receipts.
- **WP-I:** typed operation/completion core and notification waits.
- **WP-J:** file capability, staged I/O, and optional GDS adapter.
- **WP-K:** pre-opened network and IPC adapters, optional RDMA/NVSHMEM.
- **WP-L:** negative compile, ABI, fuzz, fault, CPU proxy, and hardware-gated CUDA tests.

Agents primarily add files in separately owned directories. Integration applies small shared-file patches, wires every compiler mode, runs parity and negative tests, runs CPU/CUDA transport tests, gates GDS/RDMA tests on capability, and verifies artifact hashes. No gate is accepted until deliberate sabotage makes its acceptance test fail.

## 14. Release gates

1. Honest extension and whole-call-graph enforcement in all modes.
2. CPU-simulated ABI, invariants, validation, cancellation, deadline, and faults.
3. CUDA-proxied pre-opened filesystem slice with batching and bounded waits.
4. Canonical SOSIX/POSIX convergence and removal of duplicate request arrays.
5. Direct-data probing, measurement, honest reporting, and required-mode rejection.
6. Network/IPC/input capability and namespace enforcement.
7. Mission-critical no-fallback, bounded/deterministic policy, checksums, receipts, recovery, formal/adversarial evidence, and final contract-hash verification.

## 15. Recommended first slice

Implement only `TRACE_WRITE`, `FS_READ_AT`, `FS_WRITE_AT`, and `CANCEL`, with pre-opened file capabilities, pre-registered GPU buffers, one submission and completion ring, a CPU proxy, staged `pread`/`pwrite`, Rust-seed transitive checking, and a trait-based public API. Exclude GDS, network, device graphs, and resource-syntax dependencies.

This proves the source contract, compiler gate, queue ABI, rights validation, CUDA submission, service integration, cancellation, completion, and sync/POSIX layering. Add GDS later without changing source semantics.

## 16. Final assessment

Simple supports extension syntax today, but not yet robust extension contracts. Traits and trait coherence are the correct phase-1 base; checked extensions can later become the façade.

CUDA can use a broad asynchronous subset of SOSIX: GPU-local queue/event/input/trace operations; proxied file, network, IPC, and later USB operations; and optional direct storage/network data paths. Host process, VM, signal, thread, dynamic-loading, and privileged APIs remain rejected.

```text
canonical SOSIX traits/functions
        |
checked trait impls
        |
checked extension façade
        |
compiler-owned API metadata
        |
transitive CUDA legality checker
        |
link/package backend-manifest check
        |
runtime capability and rights validation
        |
GPU-local, proxy, or direct-data backend
```

This preserves MDSOC boundaries, reuses the frozen execution/fallback vocabulary, avoids unimplemented typed facets, and provides stable parallel ownership boundaries.

## 17. Source basis

### Repository evidence

- `src/compiler_rust/parser/src/token.rs`
- `src/compiler_rust/parser/src/types_def/mod.rs`
- `src/compiler_rust/type/src/checker_check.rs`
- `src/compiler_rust/compiler/src/pipeline/execution.rs`
- `src/compiler_rust/compiler/src/monomorphize/binding_specializer.rs`
- `src/compiler/35.semantics/gpu_checker.spl`
- `doc/05_design/ui/rendering/gpu_runnable_check_design.md`
- `src/compiler/10.frontend/resource_registry.spl`
- `doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md`
- `doc/08_tracking/bug/stage3_selfhost_status_after_dedent_fix_2026-08-10.md`
- `src/os/sosix/io_state.spl`
- `src/os/sosix/io_rw.spl`
- `src/os/sosix/queue_notify.spl`
- `src/compiler/00.common/structural_contracts/offload_profile.spl`
- `src/lib/common/structural/execution/profile_types.spl`

### External primary references

- NVIDIA CUDA Programming Guide: CUDA C++ memory model and system thread scope.
- NVIDIA CUDA Programming Guide: device graph creation, upload, and launch restrictions.
- NVIDIA GPUDirect Storage cuFile API Reference.
- GPUfs: Integrating a File System with GPUs, ASPLOS 2013.
- GPUnet: Networking Abstractions for GPU Programs, OSDI 2014.
- GPU-Initiated On-Demand High-Throughput Storage Access in the BaM System Architecture, ASPLOS 2023.
- GeminiFS: A Companion File System for GPUs, FAST 2025.
- NVIDIA NVSHMEM documentation, including GPUDirect Async kernel-initiated communication.
