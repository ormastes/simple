# Bitset Specification

> <details>

<!-- sdn-diagram:id=bitset_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bitset_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bitset_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bitset_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bitset Specification

## Scenarios

### Bitset (libcu++ <bitset> parity)

#### zeros starts empty with the requested size

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = Bitset.zeros(100)
expect(b.size()).to_equal(100)
expect(b.count()).to_equal(0)
expect(b.none()).to_be(true)
expect(b.any()).to_be(false)
```

</details>

#### set/test a single bit

- var b = Bitset zeros
- b set
   - Expected: b.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = Bitset.zeros(10)
b.set(3)
expect(b.test(3)).to_be(true)
expect(b.test(2)).to_be(false)
expect(b.count()).to_equal(1)
expect(b.any()).to_be(true)
```

</details>

#### set spans multiple words (>64 bits)

- var b = Bitset zeros
- b set
- b set
- b set
- b set
   - Expected: b.count() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = Bitset.zeros(130)
b.set(0)
b.set(63)
b.set(64)
b.set(129)
expect(b.test(0)).to_be(true)
expect(b.test(63)).to_be(true)
expect(b.test(64)).to_be(true)
expect(b.test(129)).to_be(true)
expect(b.test(65)).to_be(false)
expect(b.count()).to_equal(4)
```

</details>

#### bit 63 (sign bit) is handled correctly

- var b = Bitset zeros
- b set
   - Expected: b.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = Bitset.zeros(64)
b.set(63)
expect(b.test(63)).to_be(true)
expect(b.count()).to_equal(1)
```

</details>

#### clear_bit removes a set bit

- var b = Bitset zeros
- b set
- b set
- b clear bit
   - Expected: b.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = Bitset.zeros(10)
b.set(5)
b.set(7)
b.clear_bit(5)
expect(b.test(5)).to_be(false)
expect(b.test(7)).to_be(true)
expect(b.count()).to_equal(1)
```

</details>

#### clear_bit on an unset bit is a no-op

- var b = Bitset zeros
- b set
- b clear bit
   - Expected: b.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = Bitset.zeros(10)
b.set(2)
b.clear_bit(4)
expect(b.test(2)).to_be(true)
expect(b.count()).to_equal(1)
```

</details>

#### flip toggles a bit both ways

- var b = Bitset zeros
- b flip
- b flip


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = Bitset.zeros(10)
b.flip(6)
expect(b.test(6)).to_be(true)
b.flip(6)
expect(b.test(6)).to_be(false)
```

</details>

#### set_to sets and clears by flag

- var b = Bitset zeros
- b set to
- b set to
- b set to


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = Bitset.zeros(10)
b.set_to(1, true)
b.set_to(2, true)
b.set_to(1, false)
expect(b.test(1)).to_be(false)
expect(b.test(2)).to_be(true)
```

</details>

#### all() is true only when every bit is set

- var b = Bitset zeros
- b set
- b set
- b set
   - Expected: b.count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = Bitset.zeros(3)
b.set(0)
b.set(1)
expect(b.all()).to_be(false)
b.set(2)
expect(b.all()).to_be(true)
expect(b.count()).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/compute/bitset_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Bitset (libcu++ <bitset> parity)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
