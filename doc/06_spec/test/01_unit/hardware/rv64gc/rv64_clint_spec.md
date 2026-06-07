# RV64 CLINT Unit Tests

> Unit tests for Core Local Interruptor: mtime, mtimecmp, MSIP for IPI. CLINT base address: 0x2000000.

<!-- sdn-diagram:id=rv64_clint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_clint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_clint_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_clint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 CLINT Unit Tests

Unit tests for Core Local Interruptor: mtime, mtimecmp, MSIP for IPI. CLINT base address: 0x2000000.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-CLINT-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_clint_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for Core Local Interruptor: mtime, mtimecmp, MSIP for IPI.
CLINT base address: 0x2000000.

## Scenarios

### mtime

#### initial value is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val clint = _create_clint(2)
expect(clint.mtime).to_equal(0)
```

</details>

#### tick increments mtime

1. var clint =  create clint
2. clint tick
3. clint tick
   - Expected: clint.mtime equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var clint = _create_clint(2)
clint.tick()
clint.tick()
expect(clint.mtime).to_equal(2)
```

</details>

### mtimecmp

#### write and read mtimecmp

1. var clint =  create clint
   - Expected: clint.mtimecmp[0] equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var clint = _create_clint(2)
clint.mtimecmp[0] = 1000
expect(clint.mtimecmp[0]).to_equal(1000)
```

</details>

#### per-hart mtimecmp independent

1. var clint =  create clint
   - Expected: clint.mtimecmp[0] equals `100`
   - Expected: clint.mtimecmp[1] equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var clint = _create_clint(2)
clint.mtimecmp[0] = 100
clint.mtimecmp[1] = 200
expect(clint.mtimecmp[0]).to_equal(100)
expect(clint.mtimecmp[1]).to_equal(200)
```

</details>

### Timer Interrupt

#### mtime >= mtimecmp triggers interrupt

1. var clint =  create clint
2. clint tick
   - Expected: clint.timer_interrupt_pending(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var clint = _create_clint(2)
clint.mtimecmp[0] = 5
var i = 0
while i < 5:
    clint.tick()
    i = i + 1
expect(clint.timer_interrupt_pending(0)).to_equal(true)
```

</details>

#### mtime < mtimecmp no interrupt

1. var clint =  create clint
2. clint tick
   - Expected: clint.timer_interrupt_pending(0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var clint = _create_clint(2)
clint.mtimecmp[0] = 100
clint.tick()
expect(clint.timer_interrupt_pending(0)).to_equal(false)
```

</details>

#### update mtimecmp clears interrupt

1. var clint =  create clint
2. clint tick
   - Expected: clint.timer_interrupt_pending(0) is true
   - Expected: clint.timer_interrupt_pending(0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var clint = _create_clint(2)
clint.mtimecmp[0] = 1
clint.tick()
expect(clint.timer_interrupt_pending(0)).to_equal(true)
clint.mtimecmp[0] = 100
expect(clint.timer_interrupt_pending(0)).to_equal(false)
```

</details>

### MSIP (Software Interrupt / IPI)

#### set MSIP triggers software interrupt

1. var clint =  create clint
2. clint set msip
   - Expected: clint.software_interrupt_pending(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var clint = _create_clint(2)
clint.set_msip(0, 1)
expect(clint.software_interrupt_pending(0)).to_equal(true)
```

</details>

#### clear MSIP clears interrupt

1. var clint =  create clint
2. clint set msip
3. clint set msip
   - Expected: clint.software_interrupt_pending(0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var clint = _create_clint(2)
clint.set_msip(0, 1)
clint.set_msip(0, 0)
expect(clint.software_interrupt_pending(0)).to_equal(false)
```

</details>

#### IPI: hart 0 writes MSIP[1]

1. var clint =  create clint
2. clint set msip
   - Expected: clint.software_interrupt_pending(1) is true
   - Expected: clint.software_interrupt_pending(0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var clint = _create_clint(2)
clint.set_msip(1, 1)
expect(clint.software_interrupt_pending(1)).to_equal(true)
expect(clint.software_interrupt_pending(0)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
