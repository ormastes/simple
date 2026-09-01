# MC/DC Performance and Memory Contract — Operator Manual

Executable: `test/03_system/coverage/mcdc_perf_memory_contract_spec.spl`  
Capture kinds: `artifact`  
Status: **not executed; no measurement is claimed**.

## Evidence hook

The production performance runner must populate one `PerfReceipt` from the same pinned fixture before and after the change: wall time, peak RSS, allocation count, and optimizer artifact. Missing fields fail closed. The executable checks exact integer basis-point thresholds and fixed buffer accounting; it never invents benchmark values.

## Workflow

1. **capture same-fixture timing RSS allocation and optimizer evidence** — reject an incomplete receipt.
2. Check the exact 5% (500 bp) boundary using integer arithmetic; companion release evidence must also exercise static-off 0 bp/no text delta and dynamic dormant 100 bp/enabled 1000 bp limits.
3. **check zero overhead evidence** — pin 1 MiB owner, 64 MiB global, and conservative 160-byte record accounting.

## Traceability

NFR-001..010 are attached to the executable. NFR-001/002/003/008/009 require retained real runner artifacts; NFR-004/005 are directly checked by bounded policy/accounting; NFR-006/007/010 are cross-reviewed with the provider and implementation lanes.

