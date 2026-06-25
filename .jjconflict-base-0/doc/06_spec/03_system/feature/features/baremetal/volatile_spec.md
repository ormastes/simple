# Volatile Memory Access Specification

> Volatile access ensures memory reads and writes are not optimized away.

<!-- sdn-diagram:id=volatile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=volatile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

volatile_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=volatile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Volatile Memory Access Specification

Volatile access ensures memory reads and writes are not optimized away.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BM-005 |
| Category | Language / Bare-Metal |
| Status | In Progress |
| Source | `test/03_system/feature/features/baremetal/volatile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Volatile access ensures memory reads and writes are not optimized away.
This spec uses local doubles so it can run in the interpreter/runtime
without relying on unsupported `@volatile` syntax.

## Scenarios

### Volatile Variables
_Individual volatile variable declarations._

#### Volatile at Fixed Address
_Memory-mapped registers at fixed addresses._

#### declares volatile variable at address

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cell = VolatileCell.new(0x1000, 17)
check(cell.address == 0x1000)
check(cell.read() == 17)
check(cell.reads == 1)
```

</details>

#### declares multiple registers

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = VolatileCell.new(0x2000, 1)
val control = VolatileCell.new(0x2001, 0)
val _ = status.write(3)
val _ = control.write(4)
check(status.value == 3)
check(control.value == 4)
check(status.writes == 1)
check(control.writes == 1)
```

</details>

#### Volatile Local Variables
_Volatile variables in local scope._

#### prevents read optimization

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cell = VolatileCell.new(0x3000, 9)
check(cell.read() == 9)
check(cell.read() == 9)
check(cell.reads == 2)
```

</details>

#### prevents write optimization

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cell = VolatileCell.new(0x3001, 1)
val _ = cell.write(2)
val _ = cell.write(3)
check(cell.value == 3)
check(cell.writes == 2)
```

</details>

### Volatile Structs
_Struct-level volatile declarations._

#### All Fields Volatile
_All fields behave like volatile registers._

#### declares volatile register block

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = VolatileRegisterBlock.new(0x4000)
check(block.status.address == 0x4000)
check(block.control.address == 0x4001)
check(block.data.address == 0x4002)
```

</details>

#### maps volatile struct to address

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = VolatileRegisterBlock.new(0x5000)
check(block.status.address == 0x5000)
check(block.data.read() == 255)
```

</details>

#### Mixed Volatile Struct
_Struct with volatile and nonvolatile fields._

#### overrides struct volatile with nonvolatile

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = VolatileRegisterBlock.new(0x6000)
block.cached = 11
check(block.cached == 11)
check(block.status.reads == 0)
```

</details>

#### marks specific fields volatile

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = VolatileRegisterBlock.new(0x6000)
val _ = block.status.write(7)
val _ = block.control.write(8)
check(block.status.value == 7)
check(block.control.value == 8)
```

</details>

### Volatile Semantics
_Compiler behavior with volatile._

#### Read Semantics
_Volatile reads must always fetch from memory._

#### prevents dead load elimination

1. cell read
2. cell read
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cell = VolatileCell.new(0x7000, 5)
cell.read()
cell.read()
check(cell.reads == 2)
```

</details>

#### prevents common subexpression elimination

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cell = VolatileCell.new(0x7001, 5)
val a = cell.read()
val b = cell.read()
check(a == b)
check(cell.reads == 2)
```

</details>

#### Write Semantics
_Volatile writes must always commit to memory._

#### prevents dead store elimination

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cell = VolatileCell.new(0x7002, 1)
val _ = cell.write(2)
val _ = cell.write(3)
check(cell.value == 3)
check(cell.writes == 2)
```

</details>

#### preserves write order

1. tracker full barrier
2. tracker store barrier
3. tracker load barrier
4. check log


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tracker = BarrierTracker.new()
tracker.full_barrier()
tracker.store_barrier()
tracker.load_barrier()
check_log(tracker.events, ["mfence", "sfence", "lfence"])
```

</details>

#### No Reordering
_Volatile accesses maintain program order._

#### prevents reordering across volatile

1. check log


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tracker = BarrierTracker.new()
val _ = tracker.compiler_barrier()
val _ = tracker.full_barrier()
val _ = tracker.store_barrier()
check_log(tracker.events, ["compiler", "mfence", "sfence"])
```

</details>

### Memory Barriers
_Explicit memory ordering barriers._

#### Full Barrier

#### uses mfence for full barrier

1. check log


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tracker = BarrierTracker.new()
val _ = tracker.full_barrier()
check_log(tracker.events, ["mfence"])
```

</details>

#### Load Barrier

#### uses lfence for load barrier

1. check log


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tracker = BarrierTracker.new()
val _ = tracker.load_barrier()
check_log(tracker.events, ["lfence"])
```

</details>

#### Store Barrier

#### uses sfence for store barrier

1. check log


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tracker = BarrierTracker.new()
val _ = tracker.store_barrier()
check_log(tracker.events, ["sfence"])
```

</details>

#### Compiler Barrier

#### prevents compiler reordering

1. check log


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tracker = BarrierTracker.new()
val _ = tracker.compiler_barrier()
check_log(tracker.events, ["compiler"])
```

</details>

### Volatile Intrinsics
_Low-level volatile access functions._

#### Volatile Read

#### reads byte from address

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = VolatilePort.new()
check(port.read_byte(0x10) == 0x10)
```

</details>

#### reads word from address

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = VolatilePort.new()
check(port.read_word(0x20) == 0x20)
```

</details>

#### reads dword from address

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = VolatilePort.new()
check(port.read_dword(0x30) == 0x30)
```

</details>

#### reads qword from address

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = VolatilePort.new()
check(port.read_qword(0x40) == 0x40)
```

</details>

#### Volatile Write

#### writes byte to address

1. check
2. check log


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = VolatilePort.new()
val _ = port.write_byte(0x10, 1)
check(port.last_value == 0x11)
check_log(port.events, ["write_byte"])
```

</details>

#### writes word to address

1. check
2. check log


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = VolatilePort.new()
val _ = port.write_word(0x20, 2)
check(port.last_value == 0x22)
check_log(port.events, ["write_word"])
```

</details>

#### writes dword to address

1. check
2. check log


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = VolatilePort.new()
val _ = port.write_dword(0x30, 3)
check(port.last_value == 0x33)
check_log(port.events, ["write_dword"])
```

</details>

#### writes qword to address

1. check
2. check log


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = VolatilePort.new()
val _ = port.write_qword(0x40, 4)
check(port.last_value == 0x44)
check_log(port.events, ["write_qword"])
```

</details>

### Use Cases
_Real-world volatile usage patterns._

#### Status Polling
_Polling hardware status registers._

#### polls until ready

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = VolatileCell.new(0x8000, 0)
val _ = status.write(1)
check(status.read() == 1)
```

</details>

#### DMA Buffer
_Shared memory with DMA controller._

#### reads DMA-written buffer

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dma = VolatileCell.new(0x8100, 12)
check(dma.read() == 12)
check(dma.reads == 1)
```

</details>

#### Interrupt Handler
_Shared variables between ISR and main._

#### reads ISR-modified variable

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shared = VolatileCell.new(0x8200, 5)
val _ = shared.write(9)
check(shared.read() == 9)
```

</details>

#### Hardware Register Sequence
_Registers requiring specific access sequences._

#### unlocks flash with sequence

1. check log


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tracker = BarrierTracker.new()
val _ = tracker.store_barrier()
val _ = tracker.full_barrier()
val _ = tracker.compiler_barrier()
check_log(tracker.events, ["sfence", "mfence", "compiler"])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
