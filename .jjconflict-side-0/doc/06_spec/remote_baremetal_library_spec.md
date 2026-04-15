# Remote Baremetal Library Checks

Checks the library surface that should remain usable for the `interpreter(remote(baremetal(riscv32)))` and `interpreter(remote(baremetal(arm)))` lanes even when full baremetal ELF generation is not yet available from Pure Simple.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RBLB-001 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | [doc/03_plan/trace32_x11_container_recovery_2026-03-12.md](doc/03_plan/trace32_x11_container_recovery_2026-03-12.md) |
| Research | [doc/01_research/remote_interpreter_failures_2026-03-12.md](doc/01_research/remote_interpreter_failures_2026-03-12.md) |
| Source | `test/feature/app/remote_baremetal/remote_baremetal_library_spec.spl` |
| Updated | 2026-03-30 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Checks the library surface that should remain usable for the
`interpreter(remote(baremetal(riscv32)))` and `interpreter(remote(baremetal(arm)))`
lanes even when full baremetal ELF generation is not yet available from Pure Simple.

The spec covers:

- noalloc allocator semantics through `BumpAllocator`
- fixed-capacity collection semantics through `FixedArray`, `FixedMap`, and
  `FixedSet`
- noalloc async base behavior through `NoallocScheduler` and `TimerFuture`
- semihost shortened-print readiness for QEMU RISC-V and QEMU ARM with explicit
  blocked reasons when the host or repo is not ready for a real end-to-end run
- ARM Cortex-M vector table, NVIC structure, and semihost constants
- ARM-specific semihost call opcodes (BKPT/SVC) and ADP stopped reason codes
- semihost transport strategy constants and configuration

This spec is intentionally host-aware for the semihost shortened-print lane.
It reports `skip:` or `blocked:` when custom QEMU support, fixture ELFs, or the
Pure Simple baremetal compiler path are still missing.

## Syntax

```simple
var allocator = BumpAllocator(base: 0x20000000, size: 64, offset: 0, allocated: 0)
val future = timer_after(2)
val status = qemu_riscv32_semihost_short_print_status()
val arm_status = qemu_arm_semihost_short_print_status()
```

## Examples

```simple
expect(status_is_acceptable(status)).to_equal(true)
expect(status_is_acceptable(arm_status)).to_equal(true)
expect(future.poll_timer()).to_equal(0)
expect(future.poll_timer()).to_equal(1)
```

## Scenarios

- supports bump allocation alignment and reset semantics
- supports fixed array push remove and factory sizing
- supports fixed map put update remove and probe continuity
- supports fixed set add duplicate remove and capacity tracking
- tracks cooperative scheduler task lifecycle
- advances timer futures to readiness
- keeps semihost print opcodes stable
- keeps interpreter stubs callable while qemu support is host aware
- keeps standard semihosting opcodes stable
- keeps interned print extension opcodes stable
- keeps format type IDs and test protocol handles stable
- keeps file IO mode constants stable
- keeps ARM QEMU semihost status host aware
- validates vector table structure and alignment
- checks Cortex-M exception count and stack alignment
- validates data and bss section address ranges
- supports empty vector table construction
- supports exception vector enumeration
- supports NVIC register base addresses
- keeps transport strategy constants stable
- keeps capability detection constants stable
- supports default transport configuration
