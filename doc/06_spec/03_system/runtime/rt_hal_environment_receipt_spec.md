# RT/HAL Environment Receipt — Operator Manual

Executable: `test/03_system/runtime/rt_hal_environment_receipt_spec.spl`  
Capture kinds: `exec`, `artifact`  
Status: **not executed; no host or hardware evidence is claimed**.

## Workflow

1. **execute environment instructions** — validate the closed 24-kind typed
   plan: read-env, host-identity, repo-file, allowlisted-tool, hardware-probe,
   socket lifecycle, device I/O, MMIO, IRQ lifecycle, DMA lifecycle, and clock.
2. Reject an undeclared resource and an over-limit hardware timeout.
3. Preserve unavailable board work as a typed blocked selection containing reason, prerequisite, owner, tracking ID, artifact path, and exact resume command; reject missing omission metadata.

## Traceability

| Requirement | Evidence |
|---|---|
| REQ-010 | Typed instruction and bounded plan validation |
| REQ-011 | Complete BLOCKED record and fail-closed incomplete negative |

## Physical interaction boundary

The app I/O host is the sole physical executor. Socket, device, MMIO, IRQ, DMA,
and hardware-probe instructions require a sealed physical adapter; a fake or
replay port may supply deterministic test receipts but cannot claim physical
execution. Every unavailable row remains `Blocked` or `Unsupported` with its
reason, prerequisite, owner, retained artifact, and exact resume command.
