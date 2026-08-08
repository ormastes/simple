# NFR Requirements: SimpleOS CXL Device Processes

Selected: 2026-08-02  
Selection: **NFR-B — mission-critical hardening**

## Security and correctness

- **NFR-001:** Focused adversarial tests shall accept zero unauthorized MMIO,
  IRQ, DMA, notification, reset, capability-transfer, or stale-generation
  operations.
- **NFR-002:** Driver death shall remove 100% of its BAR mappings, IRQ routes,
  IOMMU attachments/IOVAs or broker buffers, shared queue leases, and reset
  authority. Any unavailable hardware action shall fail closed and be reported.
- **NFR-003:** An IOVA shall never map outside pinned granted pages; a restarted
  driver shall never observe another process's old buffers.
- **NFR-004:** Malformed PCIe/DVSEC/CEDT, CXL mailbox/event, USB/HID, HDA, queue,
  or UNO RPC input shall not cause partial privileged state application.

## Native performance budgets

- **NFR-005:** Warm typed control IPC p99 shall be at most **75 microseconds** on
  the selected native reference host.
- **NFR-006:** `DeviceQueue` framework overhead p99 shall be at most
  **10 microseconds**, excluding hardware service time.
- **NFR-007:** Synthetic driver crash-to-ready recovery shall be at most
  **500 ms**; q35 isolated-xHCI crash-to-input-ready recovery shall be at most
  **2 seconds**.
- **NFR-008:** A default idle driver-host process shall use at most **4 MiB RSS**,
  excluding explicitly granted shared/DMA regions.
- **NFR-009:** IRQ and audio-period paths shall perform no heap allocation, text
  formatting, unbounded scan, retry sleep, or unbounded subprocess capture.

QEMU timing is diagnostic and cannot satisfy NFR-005 through NFR-008 unless the
requirement explicitly names QEMU.

## Formal and model evidence

- **NFR-010:** Checked concurrency/resource models shall cover capability
  revocation, IOVA bounds, SPSC ordering/counters, backpressure, restart
  isolation, resource lifecycle, and any claimed starvation/fairness property.
  One tested interleaving is insufficient.
- **NFR-011:** Generated proof/model artifacts shall identify their scope and
  durable handwritten theorem/constraint entry points. Regeneration shall not
  overwrite the durable proof layer.

## Evidence and reliability

- **NFR-012:** Every applicable trace shall correlate `BuildId`, `BootId`,
  `ProcessId`, `ThreadId`, `DriverInstanceId`, `DeviceNodeId`,
  `ResourceLeaseId`, `QueueId`, `QueueGeneration`, `RequestId`, `IrqSequence`,
  `TraceId`, and `SpanId`.
- **NFR-013:** Fast device events shall be fixed-size, allocation-free,
  formatting-free, bounded per CPU/driver, and expose drop counters.
- **NFR-014:** QEMU evidence bundles shall retain version/command line, serial,
  QMP JSONL, QEMU trace, SimpleOS trace, PCAP/WAV where applicable, manifest,
  topology hash, and crash bundle.
- **NFR-015:** Real-IOMMU evidence is required before any `iommu_isolated` DMA
  claim. Broker-only systems shall report `dma_brokered`.
- **NFR-016:** No wrapper may synthesize success markers, accept a stub path, or
  promote a bootstrap seed/raw-source compatibility run to production evidence.
- **NFR-017:** New/changed Simple implementation shall achieve at least 80%
  branch coverage in owned logic and contain no TODO-only, hardcoded-success,
  or placeholder-pass bodies.
- **NFR-018:** Unavailable physical rows remain active blockers with exact
  resumption contracts and cannot be counted toward feature or release PASS.

## Verification discipline

Each acceptance criterion receives one passing result per unchanged revision.
Verification stops after three fix/verify cycles and reports remaining blockers.
Release is forbidden until the full `$verify` workflow reports `STATUS: PASS`.
