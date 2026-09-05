<!-- codex-research -->
# GPU MMU Domain Research

**Date:** 2026-07-31
**Scope:** explicit object residency, bounded staged transfers, optional direct
I/O, crash-safe content-addressed storage, and placement calibration. This is
an explicit object VM, not transparent SSD-backed raw pointers or page faults.
## Findings and design implications

### 1. Explicit residency needs object lifetime and in-flight synchronization

CUDA VMM deliberately separates virtual addresses from physical allocations:
an application reserves an address range, maps backing memory, grants access,
and later unmaps it. A new mapping starts without access rights. D3D12 likewise
makes residency application-managed and requires the application to track GPU
use so a heap is evicted only after the GPU is finished. Vulkan defines handles
as valid only during object lifetime and warns that objects behind device
addresses may be accessed for as long as their backing memory is accessed.

Implications:

- `ObjectRef`/`EntityRef` should identify an arena or shard descriptor, never
  expose a durable address. Resolution checks slot generation before returning
  anything address-like. This supports **AC-1** and the frozen contracts in
  **AC-8**.
- `ResidentView<T>` should be a lease-scoped capability carrying generation and
  lease epoch. Pin count and in-flight receipt/fence state are eviction vetoes;
  completion releases the veto. Deterministic stale-access faults are safer
  than inheriting vendor APIs' undefined/invalid-lifetime behavior (**AC-1**).
- A CPU simulation can model the same descriptor transitions, epochs, fence
  completion, miss coalescing, and faults without pretending to emulate a GPU;
  this is sufficient deterministic evidence for **AC-2**.

Sources: [CUDA VMM](https://docs.nvidia.com/cuda/cuda-programming-guide/04-special-topics/virtual-memory-management.html),
[Microsoft D3D12 residency sample](https://learn.microsoft.com/en-us/samples/microsoft/directx-graphics-samples/d3d12-residency-starter-library-win32/),
[Vulkan object model](https://registry.khronos.org/vulkan/specs/latest/html/vkspec.html#fundamentals-objectmodel).

### 2. The mandatory transfer path should be a fixed pinned ring

CUDA requires page-locked host memory for asynchronous host/device copies and
documents it as a scarce resource whose overuse reduces system performance.
That rules out pinning each corpus object or letting queue depth allocate new
bounce buffers. A fixed ring of preallocated, fixed-size pinned slots provides
an exact staging ceiling and natural backpressure.

Each slot needs only a small state machine (`free -> reading -> copying ->
free`) plus completion identity. Producers wait or return a bounded-queue
result when no slot is free; they do not allocate overflow buffers. Large
artifacts stream through multiple slots. Duplicate misses should share one
in-flight load and its receipts. The steady host-memory term is therefore
`slot_count * slot_size` plus bounded queue metadata, independent of corpus
size (**AC-2**, **AC-3**).

Measure the process high-water RSS on the same executable and fixture for the
1x and 10x corpora; Linux exposes `VmHWM` as peak resident set size. Record the
runtime baseline and separately declared driver/queue and manifest-cache
allowances, then enforce the plan's complete inequality rather than merely
checking that the 10x run is "close" to 1x (**AC-3**).

Sources: [CUDA page-locked memory](https://docs.nvidia.com/cuda/cuda-programming-guide/02-basics/understanding-memory.html#page-locked-host-memory),
[CUDA 11.8 warning on pinned-memory scarcity](https://docs.nvidia.com/cuda/archive/11.8.0/cuda-c-programming-guide/index.html#page-locked-host-memory),
[Linux `/proc` memory fields](https://www.kernel.org/doc/html/latest/filesystems/proc.html#proc-pid-status).

### 3. Direct storage is a proven capability, not a backend name

NVIDIA GDS chooses among actual direct I/O, compatibility mode, and internal
staging according to GPU, filesystem, mount, driver, alignment, request size,
BAR1, and topology. Unsupported configurations can successfully execute via a
CPU bounce-buffer fallback. Thus API availability or successful reads alone
does not prove direct operation.

Implications for **AC-6**:

- Gate the direct backend on an explicit capability probe covering GPU,
  filesystem/mount, driver/library, topology, and required alignment.
- Distinguish `supported-direct`, `supported-via-fallback`, and `unsupported`.
  Only the first may satisfy direct-backend parity; absence must be reported,
  never converted into a pass.
- On capable hardware, read the same immutable `ArtifactId` through staged and
  direct paths and compare byte count, digest, and bytes. Evidence should also
  capture the selected GDS mode because cuFile may stage transparently.

Sources: [GDS Overview Guide](https://docs.nvidia.com/gpudirect-storage/overview-guide/index.html),
[GDS Design Guide](https://docs.nvidia.com/gpudirect-storage/design-guide/index.html),
[GDS O_DIRECT Requirements](https://docs.nvidia.com/gpudirect-storage/o-direct-guide/),
[GDS configuration limits](https://docs.nvidia.com/gpudirect-storage/configuration-guide/index.html).

### 4. Device-initiated I/O is a separate experimental capability

GPUDirect Async removes the CPU from initiation on supported devices, but the
documented current mechanisms are tied to specific NIC/RDMA or BlueField DMA
datapaths and require CPU-side setup plus compatible hardware/software. They
are not evidence that arbitrary SSD placement can be device-initiated.

Accordingly, `device_initiated` needs its own explicit gate and unsupported
result, separate from both staged and storage-direct capability. It must never
be selected as an implicit optimization of `staged`; the mandatory staged
backend remains the semantic reference (**AC-7**). Any future enablement must
name the concrete datapath and parity-test its bytes and completion semantics.

Sources: [DOCA GPUNetIO](https://docs.nvidia.com/doca/sdk/doca-gpunetio/),
[DOCA DMA GPU datapath](https://docs.nvidia.com/doca/archive/3-0-0/doca%2Bdma/index.html),
[CUDA 8 GPUDirect Async release note](https://docs.nvidia.com/cuda/archive/8.0/cuda-toolkit-release-notes/).

### 5. CAS recovery must publish only verified, durable state

The OCI descriptor model couples content identity with digest and byte size and
requires SHA-256 support; content is verified before consumption. SQLite's
atomic-commit protocol makes its recovery journal durable before database
changes and treats a well-formed leftover journal as recovery work after a
crash. Combined, these support a small fail-closed protocol for **AC-4**:

1. Write an immutable blob to a temporary name while computing size and digest.
2. Flush it, atomically publish it under `ArtifactId`, then append and flush a
   framed journal record containing sequence, length, and checksum.
3. Publish a manifest/checkpoint only after every referenced blob is durable.
4. Recovery accepts only complete, checksummed journal records in sequence,
   verifies referenced blob size and digest, and stops at the last complete
   checkpoint/record. A partial record or corrupt referenced blob is an error,
   not a cache miss or an invitation to consume later state.

Crash tests should cut execution at each publish boundary and mutate/truncate
both journal and blob bytes. Immutable blobs make replay idempotent; manifests
select reachable state rather than mutating blob contents.

Sources: [OCI content descriptors and digest verification](https://github.com/opencontainers/image-spec/blob/main/descriptor.md),
[SQLite atomic commit and hot-journal recovery](https://sqlite.org/atomiccommit.html).

### 6. Placement combines trace-derived reuse with measured costs

Belady's original replacement work establishes future next-use as the offline
optimum reference. Mattson et al. show how stack/reuse-distance traces evaluate
multilevel storage behavior. These are useful baselines when liveness is known,
but they do not include variable object sizes, recomputation, affinity, or
multiple residency budgets; those remain explicit planner inputs.

A deterministic planner for **AC-5** should use fixed trace order and stable
tie-breaking, reject impossible budget combinations, and compare:

- transfer estimate = measured fixed latency + bytes / measured effective
  bandwidth for the relevant tier transition;
- recompute estimate = measured producer cost;
- retention value = avoided future cost weighted by liveness/next use or reuse
  distance, then adjusted by object size and affinity group.

Calibrate on named, versioned fixed workloads and hardware profiles. CUDA
recommends GPU events for asynchronous GPU timing and effective rather than
theoretical bandwidth. For repeated measurements, report prediction error and
a stated 95% confidence interval for its mean; NIST gives the Student-t interval
when variance is estimated. The acceptance threshold must be declared before
the run, and the upper confidence limit must meet it. Persist calibration
inputs/version in `PlacementPlan` evidence so a stale profile is detectable.

Sources: [Belady, *A Study of Replacement Algorithms for a Virtual-Storage Computer*](https://doi.org/10.1147/SJ.52.0078),
[Mattson et al., *Evaluation Techniques for Storage Hierarchies*](https://doi.org/10.1147/sj.92.0078),
[CUDA performance measurement](https://docs.nvidia.com/cuda/cuda-c-best-practices-guide/index.html#performance-metrics),
[NIST confidence limits for a mean](https://www.itl.nist.gov/div898/handbook/eda/section3/eda352.htm).

## Acceptance-evidence summary

| Criteria | Domain-derived evidence |
|---|---|
| AC-1, AC-8 | generation/lease checked handle resolution; no durable raw address; fence/pin eviction veto |
| AC-2 | deterministic CPU transition model, stale faults, protected eviction, and one in-flight load per miss |
| AC-3 | fixed allocation ring, backpressure, chunked large objects, measured 1x/10x `VmHWM` inequality |
| AC-4 | immutable digest+size blobs, durable ordered journal/checkpoint, cut-point and corruption tests |
| AC-5 | stable trace/tie order, measured transfer and recompute inputs, predeclared error bound with 95% CI |
| AC-6 | explicit direct-mode proof plus staged/direct size, digest, and byte parity; unsupported is not pass |
| AC-7 | distinct device-init capability and backend selection; staged remains mandatory reference |
| AC-9--AC-11 | specs/manuals should expose the above states, budgets, failure modes, probe results, and exact evidence commands |
