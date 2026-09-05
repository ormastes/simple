# SimpleOS Memory Leveling System Test Plan

Status: selected.

Spec path: `test/03_system/os/simpleos_memory_leveling_spec.spl`

## Coverage

- REQ-001, NFR-002: profile summaries expose enabled/disabled footprint.
- REQ-002, NFR-001: bare-metal profile disables swap and migration.
- REQ-003, NFR-001, NFR-004: DMA/NIC/GPU pages reject movement.
- REQ-004: default profile demotes cold CPU pages and keeps hot pages.
- REQ-005: heterogeneous profile exposes GPU/NIC/DMA/shadow capabilities.
- REQ-006: movable ordinary pages stay separate from device-visible pages.
- REQ-006A, NFR-006: stdlib language intent stays pure and maps into the OS
  policy through the adapter.
- REQ-007, NFR-005: tests prove model decisions only; no runtime/hardware calls.

## Commands

Focused check:

```sh
bin/simple test test/03_system/os/simpleos_memory_leveling_spec.spl --mode=interpreter
```

Layout guard:

```sh
find doc/06_spec -name '*_spec.spl' | wc -l
```
