# MC/DC Parallel Recording — Operator Manual

Executable: `test/03_system/coverage/mcdc_parallel_recording_spec.spl`  
Status: **not executed in this lane**; hand-maintained mirror.

## Claim boundary

This exercises the production owner-local ring and deterministic read order. A task-runtime campaign must separately attach concurrent child receipts proving parent-authoritative aggregation under real scheduling.

## Workflow

1. **exercise independent conditions** — record two rows and require owner ID plus monotonic sequence.
2. Fill a one-slot `DropNewest` ring and require a failed second record plus exact dropped count.
3. Fill a one-slot `OverwriteOldest` ring and require the newest decision plus exact overwrite count.

## Traceability

| Requirement | Evidence |
|---|---|
| REQ-004 | Fixed capacity, explicit drop/overwrite, owner-local identity |
| REQ-014 | Deterministic sequence and oldest-to-newest reporting |

