# MC/DC Instrumentation Modes and Evidence Admission

Purpose: verify the three instrumentation policies and ensure missing controlled-binary evidence fails closed. Audience: compiler, runtime, and mission-critical release reviewers.

Source: `test/03_system/compiler/mcdc_instrumentation_modes_spec.spl`  
Evidence class: host fixture plus external binary admission  
Current execution status: **PENDING/BLOCKED** — the source-matched self-hosted compiler is unavailable. This manual is maintained by hand and is not a docgen PASS receipt.

## Preconditions

An admitted pure-Simple compiler and five source-identical controlled ELF fixtures are required for NFR acceptance. Rust-seed, stale compiler, missing binaries, and source-only inspection are inadmissible.

## Operator workflow

1. Build the controlled fixture for control, static-off, static-on, dynamic-disarmed, and dynamic-armed.
2. Run the selected assurance mode.
3. Capture binary identities, sections, allocation receipts, timings, RSS, and mappings.
4. Compare the bounded oracle.
5. Inject one missing-input or threshold violation.
6. Verify fail-closed evidence.

## Scenarios

- Static-off asserts no manifest, probe, patchpoint, or payload policy selection.
- Static-on asserts manifest plus direct probes and static payload.
- Dynamic asserts manifest plus patchpoint and no static payload.
- Missing controlled inputs must exit 2 with `ERROR nothing-checked`; it is not a skip or PASS.

## Acceptance boundary

The policy assertions exercise production configuration behavior. They do not prove NFR-001..004. Those NFRs remain pending until `scripts/check/check-mcdc-performance-gate.shs` runs with admitted binaries and produces complete retained receipts.

## Traceability

REQ-001, REQ-002, REQ-006, REQ-007, REQ-008; NFR-001 through NFR-006 and NFR-009.

## Executable source

The complete executable source remains in `test/03_system/compiler/mcdc_instrumentation_modes_spec.spl`; no executable `.spl` copy is stored under `doc/06_spec`.
