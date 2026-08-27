# Volatile Memory Access Specification

> Volatile access ensures memory reads and writes are not optimized away.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Volatile access ensures memory reads and writes are not optimized away.
This spec uses local doubles so it can run in the interpreter/runtime
without relying on unsupported `@volatile` syntax.

## Scenarios

### Volatile Variables

#### Volatile at Fixed Address
_Memory-mapped registers at fixed addresses._

#### declares volatile variable at address

- declares volatile variable at address


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares volatile variable at address")
val cell = VolatileCell.new(0x1000, 17)
check(cell.address == 0x1000)
check(cell.read() == 17)
check(cell.reads == 1)
```

</details>

#### declares multiple registers

- declares multiple registers


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares multiple registers")
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

- prevents read optimization


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prevents read optimization")
val cell = VolatileCell.new(0x3000, 9)
check(cell.read() == 9)
check(cell.read() == 9)
check(cell.reads == 2)
```

</details>

#### prevents write optimization

- prevents write optimization


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prevents write optimization")
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

- declares volatile register block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares volatile register block")
val block = VolatileRegisterBlock.new(0x4000)
check(block.status.address == 0x4000)
check(block.control.address == 0x4001)
check(block.data.address == 0x4002)
```

</details>

#### maps volatile struct to address

- maps volatile struct to address


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps volatile struct to address")
val block = VolatileRegisterBlock.new(0x5000)
check(block.status.address == 0x5000)
check(block.data.read() == 255)
```

</details>

#### Mixed Volatile Struct
_Struct with volatile and nonvolatile fields._

#### overrides struct volatile with nonvolatile

- overrides struct volatile with nonvolatile


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("overrides struct volatile with nonvolatile")
val block = VolatileRegisterBlock.new(0x6000)
block.cached = 11
check(block.cached == 11)
check(block.status.reads == 0)
```

</details>

#### marks specific fields volatile

- marks specific fields volatile


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("marks specific fields volatile")
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

- prevents dead load elimination


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prevents dead load elimination")
val cell = VolatileCell.new(0x7000, 5)
cell.read()
cell.read()
check(cell.reads == 2)
```

</details>

#### prevents common subexpression elimination

- prevents common subexpression elimination


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prevents common subexpression elimination")
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

- prevents dead store elimination


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prevents dead store elimination")
val cell = VolatileCell.new(0x7002, 1)
val _ = cell.write(2)
val _ = cell.write(3)
check(cell.value == 3)
check(cell.writes == 2)
```

</details>

#### preserves write order

- preserves write order


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves write order")
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

- prevents reordering across volatile


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prevents reordering across volatile")
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

- uses mfence for full barrier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses mfence for full barrier")
val tracker = BarrierTracker.new()
val _ = tracker.full_barrier()
check_log(tracker.events, ["mfence"])
```

</details>

#### Load Barrier

#### uses lfence for load barrier

- uses lfence for load barrier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses lfence for load barrier")
val tracker = BarrierTracker.new()
val _ = tracker.load_barrier()
check_log(tracker.events, ["lfence"])
```

</details>

#### Store Barrier

#### uses sfence for store barrier

- uses sfence for store barrier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses sfence for store barrier")
val tracker = BarrierTracker.new()
val _ = tracker.store_barrier()
check_log(tracker.events, ["sfence"])
```

</details>

#### Compiler Barrier

#### prevents compiler reordering

- prevents compiler reordering


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prevents compiler reordering")
val tracker = BarrierTracker.new()
val _ = tracker.compiler_barrier()
check_log(tracker.events, ["compiler"])
```

</details>

### Volatile Intrinsics
_Low-level volatile access functions._

#### Volatile Read

#### reads byte from address

- reads byte from address


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads byte from address")
val port = VolatilePort.new()
check(port.read_byte(0x10) == 0x10)
```

</details>

#### reads word from address

- reads word from address


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads word from address")
val port = VolatilePort.new()
check(port.read_word(0x20) == 0x20)
```

</details>

#### reads dword from address

- reads dword from address


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads dword from address")
val port = VolatilePort.new()
check(port.read_dword(0x30) == 0x30)
```

</details>

#### reads qword from address

- reads qword from address


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads qword from address")
val port = VolatilePort.new()
check(port.read_qword(0x40) == 0x40)
```

</details>

#### Volatile Write

#### writes byte to address

- writes byte to address


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes byte to address")
val port = VolatilePort.new()
val _ = port.write_byte(0x10, 1)
check(port.last_value == 0x11)
check_log(port.events, ["write_byte"])
```

</details>

#### writes word to address

- writes word to address


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes word to address")
val port = VolatilePort.new()
val _ = port.write_word(0x20, 2)
check(port.last_value == 0x22)
check_log(port.events, ["write_word"])
```

</details>

#### writes dword to address

- writes dword to address


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes dword to address")
val port = VolatilePort.new()
val _ = port.write_dword(0x30, 3)
check(port.last_value == 0x33)
check_log(port.events, ["write_dword"])
```

</details>

#### writes qword to address

- writes qword to address


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes qword to address")
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

- polls until ready


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("polls until ready")
val status = VolatileCell.new(0x8000, 0)
val _ = status.write(1)
check(status.read() == 1)
```

</details>

#### DMA Buffer
_Shared memory with DMA controller._

#### reads DMA-written buffer

- reads DMA-written buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads DMA-written buffer")
val dma = VolatileCell.new(0x8100, 12)
check(dma.read() == 12)
check(dma.reads == 1)
```

</details>

#### Interrupt Handler
_Shared variables between ISR and main._

#### reads ISR-modified variable

- reads ISR-modified variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads ISR-modified variable")
val shared = VolatileCell.new(0x8200, 5)
val _ = shared.write(9)
check(shared.read() == 9)
```

</details>

#### Hardware Register Sequence
_Registers requiring specific access sequences._

#### unlocks flash with sequence

- unlocks flash with sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unlocks flash with sequence")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `627f00959698a1c5b9abbf53f67b707b18c3d0411ae0420e7c5611e5e39b7b41`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `627f00959698a1c5b9abbf53f67b707b18c3d0411ae0420e7c5611e5e39b7b41`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `627f00959698a1c5b9abbf53f67b707b18c3d0411ae0420e7c5611e5e39b7b41`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/features/baremetal/volatile_spec.spl
mirror: doc/06_spec/03_system/feature/features/baremetal/volatile_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/baremetal/volatile_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/baremetal/volatile_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/baremetal/volatile_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares volatile variable at address' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/baremetal/volatile_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares multiple registers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/baremetal/volatile_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prevents read optimization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
