# Parallel-Agent Plan: SimpleOS CXL and Device-Process Architecture

Date: 2026-08-02  
Lane: `simpleos_cxl_device_process_architecture`  
State: **Bundle A + NFR-B selected; architecture/design is the next phase**

## Goal

Build a CXL-friendly SimpleOS device architecture in which the kernel enforces
process identity, MMIO, IRQ, DMA/IOMMU, reset, and revocation, while isolated
user-space driver processes own device protocols and policy. Prove the boundary
with xHCI/HID before implementing CXL Type 3 regions and CXL-host-mapped queues.

## Planning corrections

The supplied architectural direction is retained, with these corrections:

1. Existing process, VM-space, notification, capability, PCI, driver-runtime,
   xHCI, HDA, and QEMU mechanisms are hardened and integrated, not duplicated.
2. CXL does not imply executable device-local drivers.
3. Type 3 host-backed queue memory is `CxlHostMapped`, not `CxlCoherent`.
   `CxlDeviceCoherent` is reserved for a future proved Type 1/2 consumer.
4. QEMU is functional L0-L3 evidence only.
5. Security/adversarial checks gate every wave, not a late cleanup wave.
6. With four concurrency slots, `/root` integrates while at most three bounded
   implementation sidecars run concurrently. The A-O labels are ownership
   lanes, not fifteen simultaneous agents.

## Contract freeze

Only lane A may define or change serialization/layout until the freeze merge.

### Shared types

- `DriverManifestV2`
- `DriverNodeId` and `DeviceNode`
- `DriverPlacement`: `KernelBootstrap`, `HostIsolated`, `HostColocated`,
  `CoprocessorRemote`, `DeviceResident`
- `DriverLifecycle`
- `ResourceLease` with generation and revocation state
- `DeviceMemCapability`, `IrqCapability`, `DmaWindowCapability`,
  `SharedRegionCapability`, `NotificationCapability`, `ResetCapability`
- `IoAddressSpace`, `IommuDomain`, `IommuFaultQueue`, `DeviceAttachment`
- `DeviceQueue`, `DeviceQueueHeader`, `DeviceDescriptor`
- `QueueMemoryMode`: `HostCoherent`, `CxlHostMapped`,
  `CxlDeviceCoherent`, `DmaCoherent`, `NonCoherentDma`, `RpcCopied`
- `CxlCapabilities` with revision and per-feature fields; no global support
  boolean

### Frozen manual-facing steps

1. `Establish an isolated synthetic driver boundary`
2. `Recover a driver with a new resource generation`
3. `Deliver USB input through isolated driver processes`
4. `Discover and configure a CXL Type 3 region`
5. `Relocate a poisoned CXL-backed device queue`

### Planned setup/checker helpers

- `setup_simpleos_device_process_fixture`
- `check_device_capability_revocation`
- `check_q35_isolated_xhci_input`
- `check_q35_cxl_type3_topology`
- `check_cxl_queue_relocation`

Temporary SSpec helpers must use `assert(false)` or `fail(...)`; no placeholder
pass is permitted.

## Ownership lanes

| Lane | Exclusive ownership | Dependencies | Acceptance gate |
|---|---|---|---|
| A — contracts | New versioned device ABI, serialization, rights/errors, queue descriptor layout, placement and capability-vector schemas | selected requirements | ABI compatibility/round-trip tests; no physical pointers in protocols |
| B — identity/IPC | `src/os/kernel/types/{thread,vmspace,endpoint,notification}_types.spl`, assigned process/IPC owner files, dispatcher-authenticated sender, capability transfer and notification authorization | A freeze | distinct VM spaces; forged sender and unauthorized notification operations fail closed |
| C — resources | assigned device syscall/grant/IOMMU/MMIO/IRQ/DMA/reset owner files | A and B | out-of-range BAR/IOVA/IRQ denied; death removes mappings/routes/attachments; broker fallback reports `dma_brokered` |
| D — devmgr | new `src/os/services/devmgr/**`; integration adapters to `pcimgr` and supervisor | A, B, C, E | synthetic parent-child graph binds, crashes, revokes, resets, and rebinds at a new generation |
| E — queue runtime | new `src/os/lib/device/queue/**` and focused queue tests; descriptor layout remains A-owned | A and B notifications | SPSC wraparound, ordering, backpressure, corruption, deadline, stale generation, and recovery gates |
| F — observability | device trace schema, fixed fast event ring, metrics, crash-bundle schema, CLI readers; no `pcimgr` edits | A trace identity freeze | one request joins app -> queue -> driver -> IRQ -> completion; bounded ISR-safe record |
| G — QEMU utilities | capability probing, common QMP client, evidence-bundle collector; device scenarios remain with device lanes | A evidence schema | unsupported properties fail explicitly; bundle contains version, command, serial, QMP, trace, manifest, and device artifacts |
| H — xHCI controller | xHCI controller MMIO/IRQ/DMA migration and controller protocol | C, D, E; merge-owner split of `xhci_enum.spl` | controller owns no unrestricted physical address; crash masks/revokes/resets |
| I — USB/HID/input | USB bus/enumeration after split, generic HID report parser, HID nodes, `inputd` integration | D, E, H protocol | QMP key/mouse input reaches canonical event and compositor; malformed descriptors fail closed |
| J — PCI/CXL discovery | PCIe extended-capability walker, DVSEC, register locator, CEDT/CFMWS, topology graph | A, D, G | expected q35 CXL graph exactly matches discovered graph; result labeled QEMU-functional |
| K — CXL Type 3 | mailbox, component registers, HDM, regions, interleave, persistence, poison/RAS/hot-remove | J and C resources | volatile/persistent region operation, interleave validation, event retrieval, poison and removal recovery |
| L — CXL queue provider | `CxlHostMapped` allocator/health/fallback/relocation adapter only | E and K | metadata poison stops queue; non-CXL control reconnects DRAM replacement at new generation |
| M — HDA/audio | HDA controller process, codec process, `audiod`, shared `AudioEndpoint` | C, D, E and explicit reconciliation with active audio lane | known PCM reaches QEMU WAV; period timing/xrun and independent crash recovery pass |
| N — adversarial/model | fuzz/property/model fixtures; fixes return to owning lanes | begins with A threat model, runs every wave | capability, IOVA, queue counter/order, malformed input, restart isolation, and resource-lifecycle properties |
| O — integration/docs | merges only, dependency checks, SPipe manuals, guide/tracking consistency | all lanes | no support claim without non-mock evidence; final high-capability review complete |

## File-ownership rules

1. Lane A owns shared type definitions and serialized layouts until the freeze.
2. Lane B owns process identity and generic IPC authorization; lane C consumes
   those APIs and must not edit generic endpoint identity code.
3. Lane C owns hardware resource teardown; lane D requests teardown through the
   C contract and owns policy/state transitions only.
4. Lane E owns queue algorithms; device lanes own only typed protocol adapters.
5. Lane F owns trace schema/consumers; other lanes emit through its facade.
6. Lane G owns common harness utilities; each device lane owns scenario-specific
   expected behavior.
7. `src/os/drivers/usb/xhci_enum.spl` crosses H/I concerns today. O must split
   controller commands from USB enumeration before H and I edit in parallel.
8. M receives no audio file ownership until O reconciles the currently dirty
   `simpleos_io_audio_gpu_offload` lane. No existing audio work is folded into
   this lane implicitly.
9. N never patches production code directly; failures are routed to the owner.
10. Schema changes after freeze require compatibility analysis, ABI/version
    update, focused tests, affected-owner approval, and O merge.

## Dependency graph

```text
requirements selection
        |
        v
 A contracts + threat/evidence schema
        |
        v
 B authenticated identity/IPC
        |
        +----------+-----------+
        v          v           v
 C resources   E queues    F observability
        \          |          /
         \         |         /
          +------ D devmgr --+
                    |
          +---------+----------+
          v         v          v
       H xHCI    G QEMU     I HID parser*
          \         |          /
           + isolated USB slice
                    |
          +---------+----------+
          v                    v
       J CXL discovery       M HDA/audio**
          |
          v
       K Type 3
          |
          v
       L CXL-host-mapped queue

* I may build descriptor parser units early, but integration waits for H.
** M waits for active audio-lane reconciliation.
N adversarial/model gates every merge; O integrates and reviews every wave.
```

## Execution waves

### Wave 0 — selection and architecture freeze

Parallel sidecars (maximum three):

- A drafts rights, versions, errors, generation, placement, and serialization.
- F drafts stable trace identities and crash-bundle schema.
- N drafts threat model, fault matrix, and required concurrency/resource models.

`/root`/O reviews and freezes contracts. G performs a bounded QEMU capability
survey after the primary schema is fixed.

Exit gate:

- final feature and NFR requirements exist;
- shared types and ownership map are versioned;
- no raw physical address or process pointer crosses a public driver protocol;
- no ambiguous `cxl_supported` or `CxlCoherent` Type 3 claim;
- security and evidence expectations are attached to every later lane.

### Wave 1 — authenticated protection foundation

Sequence:

1. B completes dispatcher-derived identity, endpoint capability transfer,
   process ownership, and notification authorization.
2. After B gate, run C, E, and F in parallel.
3. D integrates those contracts after all three land.
4. N runs bounded adversarial/model gates on each merge.

Exit gate: `Establish an isolated synthetic driver boundary` and
`Recover a driver with a new resource generation` pass once each. The fixture:

- runs in a distinct `VmSpace`;
- receives bounded MMIO, IRQ, shared-region, and DMA authority;
- uses an IOVA in a real IOMMU domain, or a bounded broker buffer reported as
  `dma_brokered`;
- exchanges data through `DeviceQueue` and notifications;
- is killed while active;
- loses every mapping, IRQ route, IOMMU attachment/broker buffer, queue lease,
  and reset authority;
- restarts with a new generation and rejects stale descriptors.

### Wave 2 — isolated USB input vertical slice

Preparation: O splits `xhci_enum.spl` ownership and freezes the xHCI controller
protocol.

Parallel sidecars:

- H migrates controller MMIO/IRQ/DMA and reset.
- I completes the generic HID report parser and canonical input model without
  touching controller files.
- G builds q35 xHCI/QMP/PCAP/crash evidence utilities.

Integration then connects USB bus, HID, `inputd`, and compositor.

Exit gate: `Deliver USB input through isolated driver processes` proves:

```text
QMP input -> xHCI process -> USB bus -> HID -> inputd -> compositor
```

Then kill HID and xHCI separately. HID rebinds without controller reset; xHCI
death masks interrupts, revokes DMA/BAR authority, resets, re-enumerates, and
does not leave stuck keys/buttons.

### Wave 3 — CXL discovery and optional audio start

Parallel sidecars:

- J implements PCIe extended capabilities, CXL DVSEC/register locator,
  CEDT/CFMWS, and topology.
- G adds q35 Type 3/switch/interleave/error-injection scenarios.
- M may start only if O records the audio-lane ownership reconciliation.

Exit gate: discovered host bridge/root port/switch/endpoint/decoder topology
matches the QEMU scenario exactly and is labeled `qemu_functional_model`.
This gate makes no coherence, fabric, or performance claim.

### Wave 4 — Type 3 regions and RAS

K implements mailbox discovery, component-register access, endpoint/root/switch
HDM programming, region lifecycle, interleave, persistent capacity, health,
events, poison, and hot-remove. N fuzzes DVSEC/CEDT/mailbox/event inputs and
checks decoder/region state transitions.

Exit gate: `Discover and configure a CXL Type 3 region` passes volatile,
persistent, interleaved, poison, event, and hot-remove scenarios. No stale host
mapping or device attachment survives removal.

### Wave 5 — CXL-host-mapped queue

L adds the Type 3-backed shared-region provider after the ordinary DRAM queue
and region recovery gates are green.

Exit gate: `Relocate a poisoned CXL-backed device queue` proves:

- normal host-to-host queue operation in Type 3 memory;
- poison outside the queue does not trigger false relocation;
- data-buffer poison reports affected requests;
- metadata poison stops the queue and marks in-flight state uncertain;
- recovery uses a non-CXL kernel control endpoint;
- replacement DRAM memory is connected at a new generation;
- stale descriptors and mappings are rejected.

This is called **CXL-backed host IPC**, not a device-local driver.

### Wave 6 — physical and future hardware

These rows remain active but blocked/unsupported until the named prerequisites
exist. They are not exclusions and never count as PASS.

| Row | Prerequisites | Planned resume command | Retained artifacts | Owner / reviewer |
|---|---|---|---|---|
| UNO Q remote drivers | physical UNO Q; native QRB boot/DT/GIC/timer/SMMU/USB/storage evidence; STM32 runtime; Bridge/RPC transport | `sh scripts/check/check-simpleos-uno-q-device-process.shs --physical --strict` after the wrapper is created and self-tested | board identity, image hash, JCTL/serial transcript, RPC trace, device graph, reset evidence | L-equivalent board lane / O |
| Real CXL Type 3 | prepared server, supported firmware, real IOMMU/MSI-X, Type 3 device, vendor-safe poison/hotplug procedure | `sh scripts/check/check-simpleos-cxl-device-process.shs --real-hardware --strict` after the wrapper is created and self-tested | topology, firmware/device IDs, bandwidth/latency, RAS/hotplug logs, IOMMU faults, trace/crash bundle | K / O |
| Type 1/2 accelerator | suitable programmable endpoint, PASID/ATS/PRI/SVA support, firmware/runtime and reset control | `sh scripts/check/check-simpleos-cxl-accelerator.shs --physical --strict` after the wrapper is created and self-tested | firmware digest, attestation, queue/readback, fault/reset trace | future accelerator lane / O |
| `DeviceResident` | signed loader, isolated endpoint memory, endpoint interrupts/DMA, mailbox/bootstrap, watchdog/reset, update and attestation policy | `sh scripts/check/check-simpleos-device-resident-driver.shs --physical --strict` after the wrapper is created and self-tested | signed image, attestation, independent host/device crash/reset transcript, device-origin evidence | future firmware lane / O |

Until each planned wrapper exists, wrapper absence is itself a recorded
prerequisite blocker; source inspection or QEMU is not a substitute.

## Cross-cutting acceptance gates

### Security and lifecycle

- forged sender, wrong owner, wrong generation, out-of-range BAR/IOVA, excess
  IRQ budget, and unauthorized reset fail closed;
- every acquired grant is explicitly released or forcibly revoked;
- kill/wait paths reject `pid <= 0` before signaling/reaping;
- without IOMMU, unrestricted DMA/passthrough is denied and the bounded broker
  is reported honestly;
- driver restart never exposes a prior process's buffers.

### Queue/concurrency

- fixed-width fields and offsets/buffer IDs only;
- SPSC counters are monotonic and impossible distances reject;
- release publication and acquire consumption are documented and modeled;
- full queues return `WouldBlock`; no overwrite;
- cancellation/deadline/retry status is explicit;
- resource lifecycle and starvation/fairness claims require a model gate or an
  explicit blocker, not one interleaving test.

### Observability

Every applicable event joins `BuildId`, `BootId`, `ProcessId`, `ThreadId`,
`DriverInstanceId`, `DeviceNodeId`, `ResourceLeaseId`, `QueueId`,
`QueueGeneration`, `RequestId`, `IrqSequence`, `TraceId`, and `SpanId`.
IRQ/period fast records are fixed-size, allocation-free, formatting-free, and
bounded with drop counters.

### Evidence

QEMU bundles retain version/command, serial, QMP JSONL, QEMU trace, SimpleOS
trace, PCAP/WAV where applicable, test manifest, topology hash, and crash bundle.
No wrapper may synthesize success markers or accept a bootstrap seed/stub as
production driver-process evidence.

## Merge and review protocol

1. Each agent begins from the selected requirement and frozen contract commit.
2. Each agent owns only its listed files; unexpected dirty files are reported,
   not absorbed.
3. Each handoff names changed files, one focused passing result per acceptance
   criterion, known blockers, and any runtime-facade decision.
4. O checks dependency version, ownership, contract compatibility, and evidence
   before merge.
5. N findings return to the production owner; N does not create competing fixes.
6. `/root` is merge owner and final normal/highest-capability reviewer.
7. Generated SSpec manual quality and done marks require `/root` review; lower
   model or generated output cannot mark the lane complete.
8. Verification runs each unchanged green criterion at most once and stops
   after three fix/verify cycles for a feature.

## Artifacts expected after requirement selection

- final feature and NFR requirements;
- architecture, TUI/GUI `N/A` statement or actual device-manager UI design,
  detail design, threat model, and system-test plan;
- executable SSpec under `test/03_system/...` and Markdown manuals only under
  `doc/06_spec/...`;
- implementation and focused unit/integration/QEMU/property/model evidence;
- guide/tracking updates and final production-readiness report.

## Current handoff

Research, requirements, and planning are ready. Architecture/design and SSpec
work are next; implementation must wait for those artifacts and gates.
