*Source: `test/feature/app/remote_baremetal/remote_baremetal_library_spec.spl`*
*Last Updated: 2026-03-12*

---

# Remote Baremetal Library Checks

**Feature IDs:** #RBLB-001
**Category:** Tooling
**Difficulty:** 3/5
**Status:** Implemented
**Requirements:** N/A
**Plan:** [doc/03_plan/trace32_x11_container_recovery_2026-03-12.md](doc/03_plan/trace32_x11_container_recovery_2026-03-12.md)
**Research:** [doc/01_research/remote_interpreter_failures_2026-03-12.md](doc/01_research/remote_interpreter_failures_2026-03-12.md)

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

## Test Results (22 tests)

| Context | Tests | Status |
|---------|-------|--------|
| allocator | 1 | pass |
| collections (FixedArray, FixedMap, FixedSet) | 3 | pass |
| async (NoallocScheduler, TimerFuture) | 2 | pass |
| semihost shortened print (RISC-V) | 2 | pass |
| ARM semihost (opcodes, extensions, formats, QEMU) | 5 | pass |
| ARM Cortex-M vector table | 3 | pass |
| ARM NVIC | 3 | pass |
| semihost transport | 3 | pass |

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

## Semihost Output in TRACE32

Semihost output from the target routes to the TRACE32 **AREA** window buffer.
The T32 MCP server's `t32_setup_headless` tool enables semihosting by default:

```
SCREEN.OFF → AREA.Create MCP_OUT → AREA.Select MCP_OUT → SYStem.Option SemiHost ON
```

Read captured output with `t32_area_read(area_name: "MCP_OUT", clear: "true")`.
