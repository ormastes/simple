# Coordination Native Specification

> 1. var atom = Atom new

<!-- sdn-diagram:id=coordination_native_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=coordination_native_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

coordination_native_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=coordination_native_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coordination Native Specification

## Scenarios

### nogc_async_immut coordination native behavior

#### runs atom compare-and-set and version updates

1. var atom = Atom new
   - Expected: atom.version() equals `0`
   - Expected: atom.compare_and_set(9, 11) is false
   - Expected: atom.deref() equals `10`
   - Expected: atom.version() equals `0`
   - Expected: atom.compare_and_set(10, 11) is true
   - Expected: atom.deref() equals `11`
   - Expected: atom.version() equals `1`
   - Expected: atom.swap(\x: x + 4) equals `15`
   - Expected: atom.swap_returning_old(\x: x * 2) equals `15`
   - Expected: atom.deref() equals `30`
   - Expected: atom.version() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var atom = Atom.new(10)

expect(atom.version()).to_equal(0)
expect(atom.compare_and_set(9, 11)).to_equal(false)
expect(atom.deref()).to_equal(10)
expect(atom.version()).to_equal(0)

expect(atom.compare_and_set(10, 11)).to_equal(true)
expect(atom.deref()).to_equal(11)
expect(atom.version()).to_equal(1)

expect(atom.swap(\x: x + 4)).to_equal(15)
expect(atom.swap_returning_old(\x: x * 2)).to_equal(15)
expect(atom.deref()).to_equal(30)
expect(atom.version()).to_equal(3)
```

</details>

#### runs validated ref transitions through the atom backend

1. var ref = Ref new
   - Expected: ref.deref() equals `4`
   - Expected: ref.compare_and_set(4, -1) is false
   - Expected: ref.deref() equals `4`
   - Expected: ref.compare_and_set(4, 6) is true
   - Expected: ref.deref() equals `6`
   - Expected: rejected[0] is false
   - Expected: rejected[1] equals `6`
   - Expected: ref.deref() equals `6`
   - Expected: accepted[0] is true
   - Expected: accepted[1] equals `7`
   - Expected: ref.deref() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ref = Ref.new(4, _1 >= 0)

expect(ref.deref()).to_equal(4)
expect(ref.compare_and_set(4, -1)).to_equal(false)
expect(ref.deref()).to_equal(4)
expect(ref.compare_and_set(4, 6)).to_equal(true)
expect(ref.deref()).to_equal(6)

val rejected = ref.swap_validated(_1 - 100)
expect(rejected[0]).to_equal(false)
expect(rejected[1]).to_equal(6)
expect(ref.deref()).to_equal(6)

val accepted = ref.swap_validated(_1 + 1)
expect(accepted[0]).to_equal(true)
expect(accepted[1]).to_equal(7)
expect(ref.deref()).to_equal(7)
```

</details>

#### keeps bounded versioned snapshot history

1. var snapshot = VersionedSnapshot with history
2. snapshot update
3. snapshot update
   - Expected: snapshot.current() equals `v2`
   - Expected: snapshot.version() equals `2`
   - Expected: snapshot.version_count() equals `2`
   - Expected: snapshot.has_version(0) is false
   - Expected: snapshot.at_version(1) equals `v1`
   - Expected: frozen.get_version() equals `2`
   - Expected: frozen.get() equals `v2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var snapshot = VersionedSnapshot.with_history("v0", 2)

snapshot.update("v1")
snapshot.update("v2")

expect(snapshot.current()).to_equal("v2")
expect(snapshot.version()).to_equal(2)
expect(snapshot.version_count()).to_equal(2)
expect(snapshot.has_version(0)).to_equal(false)
expect(snapshot.at_version(1)).to_equal("v1")

val frozen = snapshot.snapshot()
expect(frozen.get_version()).to_equal(2)
expect(frozen.get()).to_equal("v2")
```

</details>

#### runs exported CAS helpers on no-GC sync atomics

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val atomic = atomic_i64_new(3)

expect(cas_compare_and_set(atomic, 2, 9)).to_equal(false)
expect(atomic.load(MemoryOrdering.SeqCst)).to_equal(3)
expect(cas_compare_and_set(atomic, 3, 9)).to_equal(true)
expect(atomic.load(MemoryOrdering.SeqCst)).to_equal(9)

expect(cas_loop(atomic, _1 + 1, 3)).to_equal(10)
expect(cas_swap_value(atomic, 12)).to_equal(10)
expect(atomic.load(MemoryOrdering.SeqCst)).to_equal(12)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_immut/coordination_native_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_immut coordination native behavior

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
