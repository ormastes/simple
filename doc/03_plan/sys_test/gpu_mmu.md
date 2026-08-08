<!-- codex-design -->
# GPU MMU System Test Plan

## Scenario

Executable spec: `test/03_system/lib/gpu/object_vm/gpu_mmu_spec.spl`
Mirrored manual: `doc/06_spec/03_system/lib/gpu/object_vm/gpu_mmu_spec.md`

| Flow step | Coverage |
|---|---|
| Create arena handles and acquire a lease | REQ-001, REQ-002 |
| Reject stale handles and protected eviction | REQ-002, REQ-003 |
| Stage an artifact through the bounded pinned ring | REQ-004, NFR-001 |
| Recover the CAS after interrupted or corrupt writes | REQ-005, NFR-004 |
| Plan placement from liveness cost and budgets | REQ-006, NFR-003, NFR-005 |
| Compare staged and direct backend bytes | REQ-007, NFR-006 |
| Keep device-initiated placement behind its gate | REQ-008 |
| Measure the fixed host RSS bound | NFR-001, NFR-002 |

## Evidence Rules

- Use `use std.spec.*`, direct value assertions, and built-in matchers only.
- CPU simulation is authoritative for portable correctness; hardware absence remains `unsupported`, never PASS.
- The RSS fixture compares 1x and 10x corpora under the same fixed budgets and records the measured maximum.
- Calibration uses fixed workloads and asserts the declared error/confidence bound.
- The generated manual exposes the eight flow steps and typed receipts/results; source mechanics remain folded.
