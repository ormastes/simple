*Source: `test/feature/app/remote_baremetal/remote_baremetal_library_spec.spl`*
*Last Updated: 2026-03-12*

---

# Remote Baremetal Library Checks

**Feature IDs:** #RBLB-001
**Category:** Tooling
**Difficulty:** 3/5
**Status:** Implemented
**Requirements:** N/A
**Plan:** [doc/plan/trace32_x11_container_recovery_2026-03-12.md](doc/plan/trace32_x11_container_recovery_2026-03-12.md)
**Research:** [doc/research/remote_interpreter_failures_2026-03-12.md](doc/research/remote_interpreter_failures_2026-03-12.md)

## Overview

Checks the library surface that should remain usable for the
`interpreter(remote(baremetal(riscv32)))` lane even when full baremetal ELF
generation is not yet available from Pure Simple.

The spec covers:

- noalloc allocator semantics through `BumpAllocator`
- fixed-capacity collection semantics through `FixedArray`, `FixedMap`, and
  `FixedSet`
- noalloc async base behavior through `NoallocScheduler` and `TimerFuture`
- semihost shortened-print readiness for QEMU RISC-V with explicit blocked
  reasons when the host or repo is not ready for a real end-to-end run

This spec is intentionally host-aware for the semihost shortened-print lane.
It reports `skip:` or `blocked:` when custom QEMU support, fixture ELFs, or the
Pure Simple baremetal compiler path are still missing.

## Syntax

```simple
var allocator = BumpAllocator(base: 0x20000000, size: 64, offset: 0, allocated: 0)
val future = timer_after(2)
val status = qemu_riscv32_semihost_short_print_status()
```

## Examples

```simple
expect(status_is_acceptable(status)).to_equal(true)
expect(future.poll_timer()).to_equal(0)
expect(future.poll_timer()).to_equal(1)
```
