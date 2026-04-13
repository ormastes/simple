<!-- codex-research -->
# NFR Requirements: x86 Dual-Arch QEMU Boot

Selected option: `NFR Option 2`

## NFR-001 Deterministic markers

Each lane shall emit deterministic lane-specific serial markers suitable for machine verification.

## NFR-002 Explicit architecture binding

Each lane shall bind to its intended target triple, ELF class, QEMU binary, machine type, and CPU model.

## NFR-003 Early-fault rejection

Validation shall fail if a lane logs early fault signatures such as `FAULT @` before the expected success markers.

## NFR-004 Probe/runtime split

Validation shall require:

- at least one passing x86_32 probe lane
- at least one explicit x86_64 full-runtime lane definition

## NFR-005 No stale-spec success

QEMU validation shall not rely solely on cached spec success; direct QEMU command verification shall remain part of investigation and regression work.

## NFR-006 Lane isolation

Success in one x86 lane shall not count as success for the other lane.
