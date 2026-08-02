# Architecture: SimpleOS Vulkan/CUDA/Adreno and Dual Knowledge Routing

## Decision

Adopt two independent composition axes.

```text
GPU session
├── VulkanDevicePort                 render/present
│   ├── QemuVulkanHostAdapter        typed host-offload evidence
│   ├── VirtioGpuVenusProtocol       staged protocol-admission evidence
│   │   └── VirtioGpuVenusAdapter    future direct guest-native evidence
│   └── AdrenoTurnipAdapter          UNO Q staged native adapter
└── ProcessingDevicePort             ProcessingIr execution
    ├── VulkanProcessingAdapter
    └── CudaHostOffloadAdapter
```

CUDA shares ProcessingIR, session correlation, invalidation, and evidence
policy with Vulkan. It does not implement Vulkan and is never named Vulkan.
Draw IR remains the rendering semantic owner; this change adds no renderer,
font path, command collector, or public platform-specific drawing API.

```text
implementation task
├── feature-group base -> exact feature expert
└── longest-prefix layer-base -> declared layer experts
    └── deterministic knowledge_selection.sdn receipt
```

Feature groups capture cross-layer intent. Layer bases capture ownership,
dependency direction, runtime constraints, and verification rules. Both are
required before design or implementation.

## MDSOC+ grouping

MDSOC grouping is hierarchical rather than limited to one small feature:

- a feature belongs to a feature group;
- related feature groups may form a domain group;
- every source path belongs to one architectural layer base;
- specialized feature and layer experts overlay their corresponding base;
- the selected group bases and overlays form a virtual capsule for the task.

This does not weaken the kernel boundary. `src/os/kernel/**` and
`src/os/drivers/**` force `mdsoc_only`. `src/os/services/**` and
`src/os/apps/**` may use MDSOC+ with an ECS business layer.

## Ports and provenance

Every execution result records backend, transport/evidence class, device and
driver identity, device handle, generation, run/frame/submission/fence/readback
IDs, checksum, mismatch count, and readback source. Admission rejects zero or
stale provenance, CPU mirrors, backend/evidence-class conflation, and missing
completion.

Evidence classes are at least `host-offload`, `guest-native`, `board-linux`,
`simpleos-native`, `software`, and `unsupported`. Promotion never crosses
classes implicitly.

## QEMU

The existing ivshmem host daemon is the selected current-host implementation.
The direct guest-native row requires a Venus-capable QEMU/virglrenderer host and
SimpleOS virtio-gpu capset, blob resource, context, fence, shared-memory, and
guest ICD support. The two rows share contracts but not completion status.

`VirtioGpuVenusProtocol` is an MDSOC-only private driver leaf beneath the
existing virtio-gpu owner. It owns protocol constants, bounded request/response
records, feature admission, Venus capset admission, identifier validation, and
the prerequisite ordering for context/blob/3D submission commands. It does not
own Vulkan semantics, Draw IR, ProcessingIR, presentation policy, or host
offload.

Protocol admission is deliberately a third state between “no Venus knowledge”
and “guest-native Vulkan.” It can establish only that a proposed transaction is
well-formed and supported by negotiated metadata. It must return a typed
blocked/unsupported result when required feature bits, capset version/size,
nonzero identifiers, bounded payloads, or prerequisite ordering are absent.
Passing this stage does not create a device handle, submit a virtqueue chain,
signal a fence, or authorize `guest-native` evidence.

Promotion to `VirtioGpuVenusAdapter` remains blocked on all of the following:

1. negotiated virtio-gpu blob-resource and context-init support;
2. Venus capset retrieval and a compatible guest ICD;
3. guest shared-memory/blob mapping with cache and lifetime ownership;
4. context/resource attachment and real 3D command submission;
5. interrupt or polling completion with correlated fence identity;
6. device-origin readback and exact CPU-oracle parity; and
7. a QEMU/virglrenderer environment that demonstrably exposes the required path.

Unit tests may prove protocol admission without hardware. Environment evidence
must separately identify QEMU, virtio-gpu and virglrenderer versions, negotiated
features/capset, guest ICD identity, submission/fence IDs, and readback origin.
Until that environment evidence passes, the direct guest-native row remains a
blocker even if every protocol unit test is green.

## UNO Q

The adapter ladder is:

1. board identity and supplied Debian boot;
2. Turnip enumeration and canonical fixture submission;
3. fence completion and device-origin readback parity;
4. audited extraction of required MSM/device/layout/IR3 knowledge;
5. SimpleOS firmware, MMU/cache, queue, fence, readback, and display owners;
6. SimpleOS-native execution of the same fixture.

Mesa code is not copied wholesale. Reused code/data must carry upstream path,
commit/version, license, local adaptation, and verification provenance.

## Knowledge selection

The registry uses stable IDs and ordered entries. Selection is exact and
fail-closed:

1. exact feature lookup;
2. feature-group base, then exact expert;
3. longest-prefix layer match for every planned/changed path;
4. layer-base, then declared experts;
5. MDSOC-only override for kernel/drivers;
6. stable-ID deduplication and lexical ordering within each class;
7. content-hash receipt persisted under `.spipe/<slug>/`.

Claude, Codex, and Gemini compare the same receipt at handoff. A changed hash,
new source layer, ambiguous prefix, or missing entry invalidates the receipt.

## MDSOC ownership

- Common ProcessingIR contract: shared tree-node capability owner.
- QEMU/Adreno/CUDA adapters: private platform leaves behind ports.
- Session selection/evidence: GPU bridge capsule policy owner.
- Knowledge registry/selector: LLM-process tooling capsule.
- Feature/layer documents: immutable knowledge inputs, not runtime policy code.

No sibling adapter imports another sibling. Public-to-next-layer calls flow
through the two ports.
