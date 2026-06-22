# Weak Pointers Specification

> Weak references provide non-owning references to values managed by a global weak reference table. When the target is invalidated (or strong count drops to zero), weak references return -1 on upgrade.

<!-- sdn-diagram:id=weak_pointers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=weak_pointers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

weak_pointers_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=weak_pointers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Weak Pointers Specification

Weak references provide non-owning references to values managed by a global weak reference table. When the target is invalidated (or strong count drops to zero), weak references return -1 on upgrade.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PTR-WEAK |
| Category | Runtime |
| Status | Implemented |
| Source | `test/03_system/feature/usage/weak_pointers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Weak references provide non-owning references to values managed by a global
weak reference table. When the target is invalidated (or strong count drops
to zero), weak references return -1 on upgrade.

## Scenarios

### Weak - create and upgrade

#### creates and upgrades weak reference

1. weak reset
   - Expected: weak_upgrade(w) equals `42`
   - Expected: weak_is_alive(w) is true
2. weak reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
weak_reset()
val tid = weak_register(42)
val w = weak_create(tid)
expect(weak_upgrade(w)).to_equal(42)
expect(weak_is_alive(w)).to_equal(true)
weak_reset()
```

</details>

### Weak - expired reference

#### returns -1 after invalidation

1. weak reset
2. weak invalidate
   - Expected: weak_upgrade(w) equals `-1`
   - Expected: weak_is_alive(w) is false
3. weak reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
weak_reset()
val tid = weak_register(99)
val w = weak_create(tid)
weak_invalidate(tid)
expect(weak_upgrade(w)).to_equal(-1)
expect(weak_is_alive(w)).to_equal(false)
weak_reset()
```

</details>

### Weak - auto-invalidate

#### invalidates when strong count drops to zero

1. weak reset
2. weak remove strong
   - Expected: weak_is_alive(w) is false
3. weak reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
weak_reset()
val tid = weak_register(50)
val w = weak_create(tid)
weak_remove_strong(tid)
expect(weak_is_alive(w)).to_equal(false)
weak_reset()
```

</details>

### Weak - multiple refs

#### both expire together

1. weak reset
   - Expected: weak_upgrade(w1) equals `77`
   - Expected: weak_upgrade(w2) equals `77`
2. weak invalidate
   - Expected: weak_upgrade(w1) equals `-1`
   - Expected: weak_upgrade(w2) equals `-1`
3. weak reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
weak_reset()
val tid = weak_register(77)
val w1 = weak_create(tid)
val w2 = weak_create(tid)
expect(weak_upgrade(w1)).to_equal(77)
expect(weak_upgrade(w2)).to_equal(77)
weak_invalidate(tid)
expect(weak_upgrade(w1)).to_equal(-1)
expect(weak_upgrade(w2)).to_equal(-1)
weak_reset()
```

</details>

### Weak - strong count tracking

#### tracks add and remove

1. weak reset
   - Expected: weak_strong_count(tid) equals `1`
2. weak add strong
   - Expected: weak_strong_count(tid) equals `2`
3. weak remove strong
   - Expected: weak_strong_count(tid) equals `1`
4. weak reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
weak_reset()
val tid = weak_register(10)
expect(weak_strong_count(tid)).to_equal(1)
weak_add_strong(tid)
expect(weak_strong_count(tid)).to_equal(2)
weak_remove_strong(tid)
expect(weak_strong_count(tid)).to_equal(1)
weak_reset()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
