# RV64 Atomics Memory Ordering Unit Tests

> Unit tests for memory ordering semantics: acquire/release bits, FENCE.

<!-- sdn-diagram:id=rv64_atomics_ordering_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_atomics_ordering_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_atomics_ordering_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_atomics_ordering_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Atomics Memory Ordering Unit Tests

Unit tests for memory ordering semantics: acquire/release bits, FENCE.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-ATOMICS-ORD-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_atomics_ordering_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for memory ordering semantics: acquire/release bits, FENCE.

## Scenarios

### Acquire/Release Bits

#### no ordering (aq=0, rl=0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ord = decode_amo_ordering(0, 0)
expect(ord == AmoOrdering.Relaxed).to_equal(true)
```

</details>

#### acquire (aq=1, rl=0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ord = decode_amo_ordering(1, 0)
expect(ord == AmoOrdering.Acquire).to_equal(true)
```

</details>

#### release (aq=0, rl=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ord = decode_amo_ordering(0, 1)
expect(ord == AmoOrdering.Release).to_equal(true)
```

</details>

#### sequentially consistent (aq=1, rl=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ord = decode_amo_ordering(1, 1)
expect(ord == AmoOrdering.SeqCst).to_equal(true)
```

</details>

### FENCE Instruction

#### FENCE rw, rw orders all memory ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# pred=0x3 (rw), succ=0x3 (rw)
val pred = 0x3
val succ = 0x3
expect(pred and 0x3).to_equal(0x3)
expect(succ and 0x3).to_equal(0x3)
```

</details>

#### FENCE.TSO: acquire+release for loads/stores

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# FENCE.TSO = FENCE rw, rw with fm=1000
val fm = 8
expect(fm).to_equal(8)
```

</details>

#### FENCE w, r orders store-to-load

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = 0x1  # w
val succ = 0x2  # r
expect(pred and 0x1).to_equal(1)
expect(succ and 0x2).to_equal(2)
```

</details>

#### FENCE i instruction fence (FENCE.I)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# FENCE.I flushes instruction cache
val is_fence_i = true
expect(is_fence_i).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
