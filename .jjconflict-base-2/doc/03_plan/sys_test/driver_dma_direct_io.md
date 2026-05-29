# Driver DMA Direct I/O System Test Plan

Feature: FR-DRIVER-0010.

## Traceability

| Requirement | Test Cases | Coverage |
|-------------|------------|----------|
| REQ-001 | explicit direct read/write request construction | Full |
| REQ-002 | aligned submit, unaligned reject | Full |
| REQ-003 | source checks cover NVMe/VirtIO adapter methods | Focused compile |
| REQ-004 | bounce-disabled reject, bounce-enabled result | Full |
| REQ-005 | timeout and cleanup authority cases | Full |
| REQ-006 | benchmark report cases | Full |

## Spec

- `test/system/driver_dma_direct_io_spec.spl`

## Pass Criteria

- `bin/simple check` passes for direct-I/O source, NVMe, VirtIO-BLK, and spec.
- `bin/simple test --force test/system/driver_dma_direct_io_spec.spl` passes.
- Stub-smell search finds no skipped test bodies, empty dummy assertions, or
  placeholder constants in touched files.
