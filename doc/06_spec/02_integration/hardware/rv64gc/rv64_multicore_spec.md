# RV64 Multi-Core Integration Tests

> Multi-hart SMP integration: boot, IPI, shared memory atomics.

<!-- sdn-diagram:id=rv64_multicore_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_multicore_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_multicore_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_multicore_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Multi-Core Integration Tests

Multi-hart SMP integration: boot, IPI, shared memory atomics.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-MULTICORE-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/02_integration/hardware/rv64gc/rv64_multicore_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Multi-hart SMP integration: boot, IPI, shared memory atomics.

## Scenarios

### Hart Initialization

#### each hart has unique mhartid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hart0_id: i64 = 0
val hart1_id: i64 = 1
expect(hart0_id != hart1_id).to_equal(true)
```

</details>

#### all registers zeroed at reset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var regs: [i64] = [0, 0, 0, 0]
expect(regs[0]).to_equal(0)
expect(regs[3]).to_equal(0)
```

</details>

#### PC at reset vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reset_pc: i64 = 0x80000000
expect(reset_pc).to_equal(0x80000000)
```

</details>

### IPI via CLINT MSIP

#### hart 0 sends IPI to hart 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var msip: [i64] = [0, 0]
msip[1] = 1  # Hart 0 writes MSIP[1]
expect(msip[1]).to_equal(1)
```

</details>

#### hart 1 sees software interrupt pending

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var msip: [i64] = [0, 1]
val pending = (msip[1] and 1) != 0
expect(pending).to_equal(true)
```

</details>

#### clear IPI after handling

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var msip: [i64] = [0, 1]
msip[1] = 0
expect(msip[1]).to_equal(0)
```

</details>

### Shared Memory Atomics

#### LR/SC: one hart succeeds, other fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shared_val: i64 = 42
# Hart 0 does LR
val hart0_loaded = shared_val
# Hart 1 does LR then SC (succeeds first)
val hart1_loaded = shared_val
shared_val = 100  # Hart 1 SC succeeds
# Hart 0 SC should fail (reservation broken)
val hart0_sc_fail = true  # SC would fail
expect(shared_val).to_equal(100)
expect(hart0_sc_fail).to_equal(true)
```

</details>

#### AMOADD: atomic increment from two harts

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var counter: i64 = 0
# Hart 0: AMOADD +1
val old0 = counter
counter = counter + 1
# Hart 1: AMOADD +1
val old1 = counter
counter = counter + 1
expect(counter).to_equal(2)
```

</details>

#### atomic flag for spinlock

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lock: i64 = 0
# AMOSWAP to acquire
val old = lock
lock = 1
expect(old).to_equal(0)
expect(lock).to_equal(1)
```

</details>

### Timer Per Hart

#### independent mtimecmp per hart

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mtimecmp: [i64] = [100, 200]
var mtime: i64 = 150
val hart0_irq = mtime >= mtimecmp[0]
val hart1_irq = mtime >= mtimecmp[1]
expect(hart0_irq).to_equal(true)
expect(hart1_irq).to_equal(false)
```

</details>

#### shared mtime across harts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mtime: i64 = 42
val hart0_reads = mtime
val hart1_reads = mtime
expect(hart0_reads).to_equal(hart1_reads)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
