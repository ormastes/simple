# Noalloc Standard Library Design

**Status:** Implemented
**Date:** 2026-02-22
**Zone:** `src/lib/nogc_async_mut_noalloc/`

## Overview

Four new modules providing heap-free capabilities for bare-metal and embedded targets:

| Module | Files | Purpose |
|--------|-------|---------|
| `collections/` | 6 | Fixed-size data structures (array, list, stack, ring buffer, map) |
| `log/` | 4 | Structured logging with multiple targets and string interning |
| `async/` | 4 | Cooperative coroutines with fixed task slots |
| `path/` | 2 | Path operations for semihosting file I/O |

**Total: 16 source files, 10 test files**

## Design Decisions

### Collections: Capacity-Checked Arrays, Not Const Generics

Simple lacks const generics (`<T, N>`), so collections use runtime capacity checks on `[i64]` arrays. The pattern:

```simple
class FixedArray:
    items: [i64]
    len: i32
    capacity: i32

    me push(value: i64) -> bool:
        if self.len >= self.capacity: return false
        # ...
```

**Rationale:** In interpreter mode, `[i64]` is dynamic but capacity-bounded. In compiled baremetal targets, the backend can lower this to stack-allocated fixed arrays when capacity is known at construction. This matches the existing pattern in `interrupt_handlers` (baremetal/interrupts.spl).

Factory functions provide common sizes: `fixed_array_8()` through `fixed_array_256()`.

### Collections: Index-Based Linked Lists

`PoolLinkedList` uses a pre-allocated node pool with index-based links (`i32` into pool array) instead of pointers:

```simple
class ListNode:
    value: i64
    next: i32    # Index, -1 = end
    prev: i32    # Index, -1 = none
```

**Rationale:** Index-based links are safer (no dangling pointers), serializable, and work identically in interpreter and compiled modes. The free list pattern (same as `FixedBlockAllocator` in `allocator.spl`) gives O(1) alloc/dealloc.

### Collections: Power-of-2 Ring Buffer

`RingBuffer` requires power-of-2 capacity for fast modulo via bitwise AND:

```simple
self.tail = (self.tail + 1) & self.mask    # Fast wraparound
```

Non-power-of-2 inputs are rounded up automatically.

### Logging: Three-Target Architecture

The logging system dispatches to three independently-selectable targets:

| Bit | Target | Transport |
|-----|--------|-----------|
| 1 | Device | Serial UART (COM1/UART0) |
| 2 | Semihost | Debugger console (BKPT/SVC/EBREAK) |
| 4 | Host file | Semihosting SYS_OPEN/SYS_WRITE |

Target selection is a bitmask: `log_init(LOG_INFO, TARGET_DEVICE | TARGET_SEMIHOST)`.

**Compressed path:** Handle-based functions (`log_info_h`, `log_info_h1`, `log_info_h2`) use string interning to send only a handle ID + parameters over semihosting, reducing bandwidth by ~89% vs. full string transmission. Leverages the existing `StringInternTable` in `baremetal/string_intern.spl`.

**Deferred output:** A 64-entry ring buffer (`log_buffer_push`/`log_buffer_flush`) allows deferring log output when the device is busy (e.g., during interrupt handlers).

### Async: Adapted from async_embedded.spl

The `async/` module is a simplified version of `nogc_async_mut/async_embedded.spl` (479 lines), stripped of generics and text usage:

| Feature | async_embedded.spl | noalloc async/ |
|---------|-------------------|----------------|
| Poll type | `Poll<T>` generic enum | `PollResult` class (i32 status + i64 value) |
| Task count | MAX_TASKS=16 | MAX_TASKS=16 |
| Tracking | Bitmask (u64) | Bitmask (i64) + bool fields |
| Future | `EmbeddedFuture<T>` | Polling via `complete_task()` |
| Timer | None | `TimerFuture` with deadline |

**Key simplification:** Since Simple's interpreter can't invoke function handles (i64), the scheduler tracks task state but actual polling is done by the application loop calling `complete_task(id, value)`. In compiled mode, the backend would wire up actual function dispatch.

### Path: Forward-Slash Convention

All paths use forward slashes exclusively. The host debugger (OpenOCD/J-Link/QEMU) handles OS-specific path translation. This avoids the complexity of Windows path handling in the embedded code.

The module provides `bm_replace_backslash()` for normalizing any backslash-containing paths received from external sources.

## Memory Budget

| Component | Size |
|-----------|------|
| FixedArray(32) | ~256 bytes |
| PoolLinkedList(32) | ~512 bytes |
| RingBuffer(64) | ~512 bytes |
| FixedStack(16) | ~128 bytes |
| FixedMap(32) | ~384 bytes |
| Logger state | ~16 bytes |
| Log buffer (64 entries) | ~512 bytes |
| NoallocScheduler (16 tasks) | ~512 bytes |
| TimerFuture | 8 bytes |
| **Total typical usage** | **~2.8 KB** |

All sizes are approximate and depend on the target architecture's word size.

## File Inventory

### Source Files (16)

```
src/lib/nogc_async_mut_noalloc/
  collections/__init__.spl
  collections/fixed_array.spl
  collections/linked_list.spl
  collections/ring_buffer.spl
  collections/fixed_stack.spl
  collections/fixed_map.spl
  log/__init__.spl
  log/logger.spl
  log/targets.spl
  log/format.spl
  async/__init__.spl
  async/poll.spl
  async/scheduler.spl
  async/timer.spl
  path/__init__.spl
  path/baremetal_path.spl
```

### Test Files (10)

```
test/unit/lib/nogc_async_mut_noalloc/
  collections/fixed_array_spec.spl
  collections/linked_list_spec.spl
  collections/ring_buffer_spec.spl
  collections/fixed_stack_spec.spl
  collections/fixed_map_spec.spl
  log/logger_spec.spl
  log/targets_spec.spl
  async/poll_spec.spl
  async/scheduler_spec.spl
  path/baremetal_path_spec.spl
```

## Integration Points

- **Allocator:** `PoolLinkedList` follows the same pool pattern as `FixedBlockAllocator` in `baremetal/allocator.spl`
- **String interning:** Logger compressed format uses `StringInternTable` from `baremetal/string_intern.spl`
- **Semihosting:** Log targets and file operations use `semi_host_call()` from `baremetal/system_api.spl`
- **Serial:** Device target delegates to `serial_print()` from `baremetal/x86/serial.spl`
- **Timer:** `TimerFuture` abstracts over platform timers (SysTick/mcycle/PIT)
