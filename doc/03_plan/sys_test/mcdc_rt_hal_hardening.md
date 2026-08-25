# System Test Plan: MC/DC, RT, and HAL Hardening

## Suites

Create executable specs and exact mirrored manuals for:

1. `coverage/mcdc_modes_and_semantics_spec.spl` — REQ-001/002/003/007/014.
2. `coverage/mcdc_enforcement_and_exclusions_spec.spl` — REQ-005/006/015.
3. `coverage/mcdc_parallel_recording_spec.spl` — REQ-004/014.
4. `coverage/mcdc_perf_memory_contract_spec.spl` — NFR-001..010.
5. `runtime/rt_hal_provider_differential_spec.spl` — REQ-008/009/014.
6. `runtime/rt_hal_environment_receipt_spec.spl` — REQ-010/011.
7. `runtime/rt_criticality_hardening_spec.spl` — REQ-012/013/015.

Each REQ has happy, boundary, and failure scenarios. Built-in matchers inspect
concrete production records; unfinished oracles call `fail(...)`. Setup is hidden
with `@inline`; primary manuals show the shared `step("...")` flows. Environment
and perf scenarios capture typed exec/artifact receipts; source strings and
screenshots alone are not evidence.

## Required evidence

Static-off IR/native inventory, truth/evaluation traces, exact pairs/exclusions,
interpreter/native identity, deterministic parallel bytes, bounded saturation,
provider effects, environment receipts, staged diagnostics, optimizer receipt,
same-fixture timing/RSS/allocation receipts, and exact basis-point boundaries.

Only the pure-Simple self-hosted runtime is admitted. BLOCKED retains reason,
prerequisite, owner, artifact paths and resume command and cannot satisfy a gate.
Each acceptance criterion is run at most once per session.
