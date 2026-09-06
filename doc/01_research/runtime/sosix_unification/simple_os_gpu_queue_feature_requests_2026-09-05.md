<!-- Saved verbatim 2026-09-05 from external research. Repo verification and stale-claim list: README_tldr.md in this directory. -->

# SimpleOS feature requests: GPU-accessible device queues

**Date:** 2026-09-05  
**Status:** Proposed backlog; not implemented, benchmarked, or filed as repository issues by this report.  
**Parent design:** [Simple runtime unification through SOSIX](simple_sosix_runtime_unification_design_plan_2026-09-05.md).  
**Inspected repository baseline:** `ormastes/simple` at `27f1973cc1548fa7cfd0994032d6186f77bcf593`.

## Purpose and decision

Add an optional SOSIX-G G2 execution profile in which an admitted GPU program can initiate selected device I/O through granted hardware queue resources. Keep SimpleOS responsible for capability admission, memory protection, queue lifecycle, accounting, revocation and recovery.

This is separate from the baseline G1 profile, where GPU requests go through a host/SimpleOS proxy. It is also separate from a direct-DMA data path initiated by CPU software. Report request initiation, data transfer, completion handling and recovery as independent properties.

The parent design's shared `SimpleRing`, task, capability, operation-ID and provider-generation contracts remain authoritative. Do not introduce a GPU-specific OS ABI or second scheduler merely to implement these requests.

## Product boundaries

| Mode | Request control | Data movement | Default status |
|---|---|---|---|
| G1 proxy | GPU request, validating CPU/SimpleOS service dispatch | Staged or qualified direct DMA | First supported integration target |
| G2 direct-data | Control may still involve CPU/SimpleOS | Qualified device-to-GPU DMA | Optional provider capability |
| G2 device-initiated | GPU initiates authorized hardware-queue work | Qualified DMA path | Experimental; hardware/trust-model-specific |

CUDA, Vulkan and Metal are execution/provider ecosystems, not proof that the corresponding vendor runtime or native driver exists on SimpleOS. Each proposed SimpleOS GPU backend needs a concrete driver/API implementation and evidence. An unavailable backend remains blocked.

## Feature backlog

### GQ-001 — Qualify a concrete GPU/endpoint/platform combination

**Priority:** prerequisite. **Owner:** SimpleOS platform/driver team with GPU-provider reviewer.

Produce a capability report naming GPU, firmware/driver, device endpoint, bus topology, DMA address reachability, memory types, synchronization primitives, queue/doorbell access mechanisms, and available isolation. Include the target operating mode: G1, direct-data only, or device-initiated.

Do not use a generic "PCIe supported" flag as proof of peer-to-peer access. Do not infer a live CPU/GPU atomic protocol from addressability alone. A configuration may support direct data without permitting GPU queue initiation.

**Acceptance:** an actual native probe validates the relevant memory and command paths; unsupported or inaccessible paths report a specific blocked capability. Emulator results are separately labeled and cannot qualify physical peer-to-peer DMA.

### GQ-002 — Grant a capability-scoped device queue lease

**Priority:** prerequisite. **Owner:** SOSIX capability/service owner with device-driver reviewer.

Add a service operation that grants a queue lease to an admitted instance and producer domain. The lease identifies queue/provider generation, lifetime, permitted operations, authority scope, capacity/credits, priority/deadline policy and memory-registration constraints.

A lease is not a raw integer queue ID that any process can reuse. Use the common capability handle representation. Keep administrative queues, arbitrary MMIO and device-global configuration out of the normal GPU lease.

**Acceptance:** unauthorized clients, stale generations, excess queues, unsupported producer domains and rights escalation are rejected before exposure. Revoking one lease cannot grant access to another client's resources.

### GQ-003 — Register and pin GPU-accessible DMA buffers

**Priority:** prerequisite. **Owner:** memory/DMA subsystem with GPU-provider reviewer.

Reuse registered-buffer contracts and memory-leveling ownership. Record allocation domain, device access rights, offset/length/alignment bounds, relevant mappings and pins, coherency protocol and retirement authority.

Memory cannot migrate, be remapped, freed or reused while an operation or queue may access it. Registration failure is explicit; a direct-required profile cannot secretly replace registration with an unreported CPU bounce buffer.

**Acceptance:** invalid ranges, arithmetic overflow, stale registrations, wrong directions and premature unmap are rejected. Forced cancellation/reset tests demonstrate that late DMA cannot target a recycled allocation.

### GQ-004 — Establish an enforceable producer trust model

**Priority:** security prerequisite. **Owner:** kernel/security and device owner jointly.

Record which mechanism prevents an admitted producer from issuing unauthorized commands after queue grant. Options are hardware-enforced device/function/resource isolation, or a trusted admitted producer under an explicitly restricted threat model. Where the device lacks the necessary isolation for an untrusted producer, retain a validating intermediary.

An IOMMU restricts DMA addresses, not every device command's operation or logical resource. A read-only data-memory mapping is not proof that a GPU cannot issue a write command. A software validator before grant does not constrain a mutable raw SQ afterward.

**Acceptance:** attempt forbidden opcode, queue, namespace/block range, DMA target and administrative access within the declared test model. Each must be hardware-unreachable, rejected by an unavoidable intermediary, or explicitly outside the trusted-producer deployment—not falsely reported as sandboxed.

### GQ-005 — Implement backend-specific queue and doorbell publication

**Priority:** first data-path implementation. **Owner:** native GPU and endpoint driver owners.

Provide a publication protocol describing queue entry construction, memory ordering, cache visibility, doorbell access, completion observation and batch ownership. Where a hardware ring differs from SimpleRing, use an explicit provider adapter rather than claim binary identity.

The provider owns multi-producer aggregation if needed; the shared contract retains bounded admission and unique lifecycle ownership. A single producer's reservation must not publish another producer's half-written descriptor.

**Acceptance:** randomized producer delays, wraparound, queue saturation, split batches and memory visibility tests pass on real hardware. Unsupported atomics or MMIO accesses cause profile rejection rather than fallback to undefined behavior.

### GQ-006 — Integrate exact completion and resource retirement

**Priority:** first data-path implementation. **Owner:** async lifecycle owner with device-driver reviewer.

Map hardware completions to canonical instance/ring/slot/generation identities. Retain operation, buffer and provider-generation pins until the provider confirms physical retirement. Consumer timeout and cancellation remain distinct from retirement.

Reserve bounded completion/control capacity before admitting work. Completion overflow cannot silently discard an accepted request. Late, duplicate and stale completions are diagnostic events, not authority to mutate a new operation.

**Acceptance:** exactly one logical terminal outcome per committed single-shot request; no incorrect task wake; no resource release before retirement; generation exhaustion fails closed.

### GQ-007 — Revoke, quiesce, drain and reset safely

**Priority:** required before user-facing enablement. **Owner:** driver lifecycle and SOSIX capability owners.

Define an ordered shutdown:

```text
stop new admission
-> revoke new producer access where enforceable
-> stop/quiesce producer and device queue
-> drain or explicitly account for outstanding commands
-> establish no further DMA/queue access
-> release registered memory and mappings
-> retire queue identity/provider generation
```

Generation invalidation prevents software-token reuse but does not stop an already issued DMA. If quiescence cannot be established, quarantine resources or reset at the required isolation scope; do not simply free memory.

**Acceptance:** GPU loss, endpoint reset, proxy/service death, timeout, client termination and forced revocation each complete safely or produce an explicit quarantined state. Neighboring clients retain their promised isolation.

### GQ-008 — Prevent scheduling and dependency deadlocks

**Priority:** required before persistent execution. **Owner:** GPU scheduling and runtime executor owners.

Build a dependency model between resident GPU work, device completions, host/SimpleOS service work and continuation submissions. Reject or transform a cycle in which a waiting persistent kernel prevents a required continuation from running.

Support dispatch-boundary continuation as the baseline. Advanced persistent paths require a proven progress mechanism and declared resource reservations. Quotas prevent a producer from consuming every completion/control credit.

**Acceptance:** saturation and adversarial dependency tests preserve progress or fail admission predictably. A watchdog firing is a failure/recovery observation, not evidence of a bounded scheduling guarantee.

### GQ-009 — Define storage semantics above raw block access

**Priority:** before exposing direct file I/O. **Owner:** VFS/filesystem/storage with SOSIX reviewer.

Start with an isolated raw-block or read-only experiment only under the approved trust model. To expose canonical file `read_at`/`write_at`, add authorized stable mapping/extent leases, coherence with other readers/writers, truncation/remap invalidation, partial-I/O reporting and explicit durability operations.

A cached physical-block list must not survive file remapping or revocation without an enforcing invalidation protocol. Write completion and durable completion are separate facts where the device/filesystem distinguishes them.

**Acceptance:** concurrent truncation/remapping/revocation and reset cannot expose unrelated file data. Write/flush ordering and crash/recovery behavior match the documented service contract. Raw-block success is never reported as full filesystem correctness.

### GQ-010 — Keep input, display and general devices capability-specific

**Priority:** later expansion. **Owner:** device/service owners.

Do not assume storage queue mechanisms apply unchanged to keyboard, mouse, display or USB. Normalized keyboard/mouse/text events should initially arrive through the existing SOSIX input service, then be consumed by the GPU from admitted batches.

Direct display/device paths must preserve focus, device authority, event ordering, hotplug/reset behavior and surface generations. Each endpoint family supplies its own allowed operation set and buffer lifetime rules.

**Acceptance:** expansion adds per-family conformance and authority tests without weakening existing input/display semantics or introducing raw device access into application code.

### GQ-011 — Expose independent control/data-path evidence

**Priority:** required for every qualification claim. **Owner:** verification/performance team.

Record who initiates requests, submits native queues, transfers payloads, processes completions, and performs recovery. Count CPU proxy requests, staged bytes, direct DMA bytes, GPU submissions, queue kicks, allocation events and retirement delay. Include producer provenance and independently checked payloads.

A direct-data path may legitimately have CPU control work; label it accurately. A device-initiated-required profile rejects or clearly fails when it cannot meet its requirement. It cannot silently degrade and still report the strict profile as accepted.

**Acceptance:** evidence from a real target distinguishes G1, G2 direct-data and G2 device-initiated behavior. A passing source guard, generated receipt, queue write or mock endpoint is not sufficient.

### GQ-012 — Integrate compiler and loader admission

**Priority:** required before public deployment. **Owner:** compiler legality and loader/provider teams.

Emit and validate required SOSIX operation/interface/transport profiles from resolved device code. Preserve canonical SOSIX-G metadata and resource rights. A provider that cannot meet memory visibility, authority, retirement or progress requirements is rejected before kernel execution.

The loader grants only the capabilities specified for the admitted instance and pins the provider generation for active code and operations. Updating a driver/provider cannot invalidate in-flight task state or registered mappings.

**Acceptance:** missing/changed capabilities, unknown externs, alias-based host-call bypass, incompatible transport versions and stale provider generations fail with actionable diagnostics.

## Dependencies and delivery order

```text
GQ-001 qualification
   -> GQ-002 queue lease + GQ-003 DMA registration + GQ-004 authority
      -> GQ-005 publication + GQ-006 completion/retirement
         -> GQ-007 recovery + GQ-008 progress
            -> GQ-011 evidence + GQ-012 deployment admission
               -> first qualified raw-device release
                  -> GQ-009 filesystem semantics
                  -> GQ-010 other endpoint families
```

GQ-011 and GQ-012 design work starts early; their release gates run against the complete path. GQ-004 is not deferred until after a fast prototype has become the default architecture.

## Required first demonstration

Use one explicitly admitted GPU producer and one isolated endpoint/queue, fixed registered buffers, and a bounded operation set. The demonstration must include successful data transfer and negative cases: full queue, bad/stale handle, invalid buffer range, forbidden authority, cancellation, timeout, delayed completion, endpoint reset and client termination.

Retain a G1 implementation as the correctness comparator and supported fallback **only when the deployment policy permits fallback**. Compare performance with like-for-like payloads and durability semantics; do not label staged vs direct differences as language overhead.

The release record states the exact hardware, driver, SimpleOS artifact and source revision, producer trust model, supported operation set, unsupported scenarios and evidence IDs. No general support claim is inferred beyond that scope.

## Definition of done

A configuration is qualified only when it can prove bounded admission, permitted device effects, correct memory visibility, exact completion, safe retirement, recovery and declared progress. The core SOSIX runtime migration can ship independently of this extension.

## Research basis

The parent document's source ledger contains the primary references: BaM for GPU-initiated storage research; Arrakis for separating operating-system control and direct data paths; NVIDIA GDS documentation for distinguishing direct data from CPU control; and Linux PCI peer-to-peer DMA documentation for topology/provider constraints. These are architectural inputs, not evidence that SimpleOS already has this implementation.
