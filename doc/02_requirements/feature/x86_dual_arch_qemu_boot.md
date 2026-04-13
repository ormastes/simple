<!-- codex-research -->
# Feature Requirements: x86 Dual-Arch QEMU Boot

Selected option: `Option A`

## REQ-001 Explicit x86 lanes

The system shall expose x86_32 and x86_64 as separate first-class QEMU/boot lanes.

## REQ-002 x86_32 boot lane

The x86_32 lane shall be the conservative Multiboot/BIOS-compatible boot and probe lane.

## REQ-003 x86_64 runtime lane

The x86_64 lane shall be the full runtime/browser/desktop lane and shall retain its own long-mode wrapper/runtime boundary.

## REQ-004 Explicit QEMU tuples

The runner and test design shall keep explicit per-lane QEMU tuples:

- x86_32: `qemu-system-i386`, `pc`, `qemu32`
- x86_64: `qemu-system-x86_64`, `q35`, `qemu64`

## REQ-005 Shared logic above boot boundary

Browser and desktop application logic shall be shared only above the boot/runtime boundary.

## REQ-006 No false equivalence

The design shall not treat an ELF32-wrapped x86_64 artifact as the canonical proof of native x86_64 support.

## REQ-007 Lane-visible naming

Target constructors, logs, and documentation shall make the lane identity explicit at the x86_32/x86_64 level.

## REQ-008 Staged delivery

Implementation shall prioritize:

1. stable x86_32 probe visibility
2. explicit x86_64 wrapper/runtime investigation lane
3. later restoration of x86_64 browser/desktop runtime validation
