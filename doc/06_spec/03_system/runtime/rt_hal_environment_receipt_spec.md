# RT/HAL Environment Receipt — Operator Manual

Executable: `test/03_system/runtime/rt_hal_environment_receipt_spec.spl`  
Capture kinds: `exec`, `artifact`  
Status: **not executed; no host or hardware evidence is claimed**.

## Workflow

1. **execute environment instructions** — validate a typed bounded environment-read plan with no process authority.
2. Reject an undeclared resource and an over-limit hardware timeout.
3. Preserve unavailable board work as a typed blocked selection containing reason, prerequisite, owner, tracking ID, artifact path, and exact resume command; reject missing omission metadata.

## Traceability

| Requirement | Evidence |
|---|---|
| REQ-010 | Typed instruction and bounded plan validation |
| REQ-011 | Complete BLOCKED record and fail-closed incomplete negative |

