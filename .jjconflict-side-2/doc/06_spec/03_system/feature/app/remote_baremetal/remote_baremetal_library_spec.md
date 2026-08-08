# Remote Baremetal Library Checks

> Checks the library surface that should remain usable for the `interpreter(remote(baremetal(riscv32)))` and `interpreter(remote(baremetal(arm)))` lanes even when full baremetal ELF generation is not yet available from Pure Simple.

<!-- sdn-diagram:id=remote_baremetal_library_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=remote_baremetal_library_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

remote_baremetal_library_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=remote_baremetal_library_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

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
| Source | `test/03_system/feature/app/remote_baremetal/remote_baremetal_library_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

### Remote baremetal library readiness

#### allocator

#### supports bump allocation alignment and reset semantics

1. var allocator = BumpAllocator
   - Expected: first equals `0x20000000`
   - Expected: allocator.total_allocated() equals `8`
   - Expected: allocator.remaining() equals `56`
   - Expected: second equals `0x20000010`
   - Expected: allocator.total_allocated() equals `24`
   - Expected: allocator.remaining() equals `40`
2. allocator reset
   - Expected: allocator.total_allocated() equals `0`
   - Expected: allocator.remaining() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var allocator = BumpAllocator(base: 0x20000000, size: 64, offset: 0, allocated: 0)

val first = allocator.alloc(5)
expect(first).to_equal(0x20000000)
expect(allocator.total_allocated()).to_equal(8)
expect(allocator.remaining()).to_equal(56)

val second = allocator.alloc_aligned(4, 16)
expect(second).to_equal(0x20000010)
expect(allocator.total_allocated()).to_equal(24)
expect(allocator.remaining()).to_equal(40)

allocator.reset()
expect(allocator.total_allocated()).to_equal(0)
expect(allocator.remaining()).to_equal(64)
```

</details>

#### collections

#### supports fixed array push remove and factory sizing

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = FixedArray.new(3)
expect(arr.push(10)).to_equal(true)
expect(arr.push(20)).to_equal(true)
expect(arr.push(30)).to_equal(true)
expect(arr.push(40)).to_equal(false)
expect(arr.remove(1)).to_equal(20)
expect(arr.size()).to_equal(2)
expect(arr.get(0)).to_equal(10)
expect(arr.get(1)).to_equal(30)

val arr8 = fixed_array_8()
expect(arr8.capacity).to_equal(8)
```

</details>

#### supports fixed map put update remove and probe continuity

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = FixedMap.new(8)
expect(map.put(1, 10)).to_equal(true)
expect(map.put(9, 90)).to_equal(true)
expect(map.put(1, 11)).to_equal(true)
expect(map.get(1)).to_equal(11)
expect(map.get(9)).to_equal(90)
expect(map.contains(9)).to_equal(true)
expect(map.remove(1)).to_equal(true)
expect(map.contains(1)).to_equal(false)
expect(map.get(9)).to_equal(90)
```

</details>

#### supports fixed set add duplicate remove and capacity tracking

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val set = FixedSet.new(3)
expect(set.add(5)).to_equal(true)
expect(set.add(7)).to_equal(true)
expect(set.add(5)).to_equal(true)
expect(set.size()).to_equal(2)
expect(set.contains(7)).to_equal(true)
expect(set.remove(5)).to_equal(true)
expect(set.contains(5)).to_equal(false)
expect(set.capacity()).to_equal(3)
```

</details>

#### async

#### tracks cooperative scheduler task lifecycle

1. sched complete task
   - Expected: sched.is_task_complete(task1) is true
   - Expected: sched.task_result(task1) equals `77`
   - Expected: sched.has_active_incomplete() is true
2. sched complete task
   - Expected: sched.count_completed() equals `2`
3. sched cleanup completed
   - Expected: sched.task_count() equals `0`
   - Expected: sched.is_idle() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sched = NoallocScheduler.new()
expect(sched.is_idle()).to_equal(true)

val task0 = sched.spawn(100, 0)
val task1 = sched.spawn(200, 1)
expect(task0).to_equal(0)
expect(task1).to_equal(1)
expect(sched.task_count()).to_equal(2)
expect(MAX_TASKS).to_equal(16)

sched.complete_task(task1, 77)
expect(sched.is_task_complete(task1)).to_equal(true)
expect(sched.task_result(task1)).to_equal(77)
expect(sched.has_active_incomplete()).to_equal(true)

sched.complete_task(task0, 33)
expect(sched.count_completed()).to_equal(2)

sched.cleanup_completed()
expect(sched.task_count()).to_equal(0)
expect(sched.is_idle()).to_equal(true)
```

</details>

#### advances timer futures to readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start = timer_now()
val elapsed = timer_elapsed(start)
expect(elapsed).to_be_greater_than(0)

val future = timer_after(2)
expect(future.poll_timer()).to_equal(0)
expect(future.poll_timer()).to_equal(1)
```

</details>

#### semihost shortened print

#### keeps semihost print opcodes stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TARGET_DEVICE).to_equal(1)
expect(TARGET_SEMIHOST).to_equal(2)
expect(TARGET_HOST_FILE).to_equal(4)
expect(SYS_WRITE_HANDLE).to_equal(0x100)
expect(SYS_WRITE_HANDLE_P1).to_equal(0x101)
expect(SYS_WRITE_HANDLE_P2).to_equal(0x102)
```

</details>

#### keeps interpreter stubs callable while qemu support is host aware

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val riscv_status = qemu_riscv32_semihost_short_print_status()
val arm_status = qemu_arm_semihost_short_print_status()
expect(status_is_acceptable(riscv_status)).to_equal(true)
expect(status_is_acceptable(arm_status)).to_equal(true)
expect(TARGET_SEMIHOST).to_equal(2)
```

</details>

#### ARM semihost

#### keeps standard semihosting opcodes stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SYS_OPEN).to_equal(0x01)
expect(SYS_CLOSE).to_equal(0x02)
expect(SYS_WRITEC).to_equal(0x03)
expect(SYS_WRITE0).to_equal(0x04)
expect(SYS_WRITE).to_equal(0x05)
expect(SYS_READ).to_equal(0x06)
expect(SYS_EXIT).to_equal(0x18)
expect(SYS_EXIT_EXTENDED).to_equal(0x20)
```

</details>

#### keeps interned print extension opcodes stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SYS_WRITE_HANDLE).to_equal(0x100)
expect(SYS_WRITE_HANDLE_P1).to_equal(0x101)
expect(SYS_WRITE_HANDLE_P2).to_equal(0x102)
expect(SYS_WRITE_HANDLE_P3).to_equal(0x103)
expect(SYS_WRITE_HANDLE_PN).to_equal(0x104)
```

</details>

#### keeps format type IDs and test protocol handles stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(FMT_NONE).to_equal(0)
expect(FMT_INT32).to_equal(3)
expect(FMT_FLOAT64).to_equal(10)
expect(FMT_TEXT).to_equal(19)
expect(FMT_HEX32).to_equal(15)
expect(HANDLE_TEST_START).to_equal(0x7FFF0001)
expect(HANDLE_TEST_PASS).to_equal(0x7FFF0002)
expect(HANDLE_TEST_FAIL).to_equal(0x7FFF0003)
expect(HANDLE_TEST_END).to_equal(0x7FFF0004)
```

</details>

#### keeps file IO mode constants stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MODE_READ).to_equal(0)
expect(MODE_WRITE).to_equal(4)
```

</details>

#### keeps ARM QEMU semihost status host aware

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm_status = qemu_arm_semihost_short_print_status()
expect(status_is_acceptable(arm_status)).to_equal(true)
```

</details>

#### ARM Cortex-M vector table

#### validates vector table structure and alignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vt = arm_create_vector_table()
expect(vt.initial_sp).to_equal(ARM_STACK_TOP)
expect(vt.reset).to_equal(0x08000100)
expect(vt.nmi).to_equal(0x08000200)
expect(vt.hard_fault).to_equal(0x08000300)
expect(vt.reserved1).to_equal(0)
expect(vt.reserved2).to_equal(0)
expect(vt.reserved3).to_equal(0)
expect(vt.reserved4).to_equal(0)
expect(vt.reserved5).to_equal(0)
```

</details>

#### checks Cortex-M exception count and stack alignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm_check_stack_alignment(ARM_STACK_TOP)).to_equal(true)
expect(arm_check_stack_alignment(0x20000004)).to_equal(false)
expect(arm_check_vector_alignment(0)).to_equal(true)
expect(arm_check_vector_alignment(128)).to_equal(true)
expect(arm_check_vector_alignment(64)).to_equal(false)
```

</details>

#### validates data and bss section address ranges

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm_check_data_init(0x20000000, 0x20001000)).to_equal(true)
expect(arm_check_data_init(0x08000000, 0x08001000)).to_equal(false)
expect(arm_check_bss_init(0x20001000, 0x20002000)).to_equal(true)
expect(arm_check_bss_init(0x10000000, 0x10001000)).to_equal(false)
```

</details>

#### ARM NVIC

#### supports empty vector table construction

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_vt = VectorTable(
    initial_sp: 0x20020000, reset: 0, nmi: 0,
    hard_fault: 0, mem_manage: 0, bus_fault: 0,
    usage_fault: 0, reserved1: 0, reserved2: 0,
    reserved3: 0, reserved4: 0, svcall: 0,
    debug_mon: 0, reserved5: 0, pendsv: 0, systick: 0
)
expect(empty_vt.initial_sp).to_equal(0x20020000)
expect(empty_vt.reset).to_equal(0)
expect(empty_vt.nmi).to_equal(0)
expect(empty_vt.hard_fault).to_equal(0)
```

</details>

#### supports exception vector enumeration

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reset = ExceptionVector.Reset
val nmi = ExceptionVector.Nmi
val hard_fault = ExceptionVector.HardFault
val systick = ExceptionVector.SysTick
expect(reset.to_i64()).to_equal(1)
expect(nmi.to_i64()).to_equal(2)
expect(hard_fault.to_i64()).to_equal(3)
expect(systick.to_i64()).to_equal(15)
expect(reset.name()).to_equal("Reset")
expect(nmi.name()).to_equal("NMI")
expect(hard_fault.name()).to_equal("HardFault")
expect(systick.name()).to_equal("SysTick")
```

</details>

#### supports NVIC register base addresses

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nvic = NvicRegisters(
    iser_base: 0xE000E100, icer_base: 0xE000E180,
    ispr_base: 0xE000E200, icpr_base: 0xE000E280,
    iabr_base: 0xE000E300, ipr_base: 0xE000E400
)
expect(nvic.iser_base).to_equal(0xE000E100)
expect(nvic.icer_base).to_equal(0xE000E180)
expect(nvic.ispr_base).to_equal(0xE000E200)
expect(nvic.icpr_base).to_equal(0xE000E280)
expect(nvic.iabr_base).to_equal(0xE000E300)
expect(nvic.ipr_base).to_equal(0xE000E400)
```

</details>

#### semihost transport

#### keeps transport strategy constants stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TRANSPORT_WRITEC).to_equal(1)
expect(TRANSPORT_WRITE0).to_equal(2)
expect(TRANSPORT_WRITE).to_equal(3)
expect(TRANSPORT_BATCH_N).to_equal(4)
expect(TRANSPORT_BUFFERED).to_equal(5)
expect(TRANSPORT_UART).to_equal(6)
expect(TRANSPORT_RAW_BINARY).to_equal(7)
expect(TRANSPORT_INTERNED).to_equal(8)
```

</details>

#### keeps capability detection constants stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CAP_WRITEC).to_equal(1)
expect(CAP_WRITE0).to_equal(2)
expect(CAP_WRITE).to_equal(4)
expect(CAP_UART).to_equal(8)
expect(CAP_INTERNED).to_equal(16)
expect(RAW_BINARY_MAGIC).to_equal(0x53)
```

</details>

#### supports default transport configuration

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = semihost_config_default()
expect(config.preferred_transport).to_equal(1)
expect(config.batch_size).to_equal(3)
expect(config.buffer_capacity).to_equal(0)
expect(config.uart_base_addr).to_equal(0x10000000)
expect(config.auto_detect).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [[doc/03_plan/trace32_x11_container_recovery_2026-03-12.md](doc/03_plan/trace32_x11_container_recovery_2026-03-12.md)]([doc/03_plan/trace32_x11_container_recovery_2026-03-12.md](doc/03_plan/trace32_x11_container_recovery_2026-03-12.md))
- **Research:** [[doc/01_research/remote_interpreter_failures_2026-03-12.md](doc/01_research/remote_interpreter_failures_2026-03-12.md)]([doc/01_research/remote_interpreter_failures_2026-03-12.md](doc/01_research/remote_interpreter_failures_2026-03-12.md))


</details>
