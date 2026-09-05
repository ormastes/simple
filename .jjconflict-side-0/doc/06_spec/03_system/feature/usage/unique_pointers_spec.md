# Unique Pointers Specification

> UniquePtr provides exclusive ownership semantics via cooperative move tracking. Since Simple copies on assignment, unique_move returns a new valid ptr and marks the old one as moved internally.

<!-- sdn-diagram:id=unique_pointers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unique_pointers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unique_pointers_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unique_pointers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unique Pointers Specification

UniquePtr provides exclusive ownership semantics via cooperative move tracking. Since Simple copies on assignment, unique_move returns a new valid ptr and marks the old one as moved internally.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PTR-UNIQUE |
| Category | Runtime |
| Status | Implemented |
| Source | `test/03_system/feature/usage/unique_pointers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

UniquePtr provides exclusive ownership semantics via cooperative move tracking.
Since Simple copies on assignment, unique_move returns a new valid ptr and
marks the old one as moved internally.

## Scenarios

### Unique - create and read

#### creates and reads value

1. unique reset
   - Expected: unique_get(p) equals `42`
   - Expected: unique_is_valid(p) is true
2. unique reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unique_reset()
val p = unique_new(42, "test")
expect(unique_get(p)).to_equal(42)
expect(unique_is_valid(p)).to_equal(true)
unique_reset()
```

</details>

### Unique - move ownership

#### transfers ownership on move

1. unique reset
   - Expected: unique_is_valid(p1) is false
   - Expected: unique_is_valid(p2) is true
   - Expected: unique_get(p2) equals `100`
2. unique reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unique_reset()
val p1 = unique_new(100, "moveable")
val p2 = unique_move(p1)
expect(unique_is_valid(p1)).to_equal(false)
expect(unique_is_valid(p2)).to_equal(true)
expect(unique_get(p2)).to_equal(100)
unique_reset()
```

</details>

### Unique - moved returns -1

#### get on moved ptr returns -1

1. unique reset
   - Expected: unique_get(p) equals `-1`
2. unique reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unique_reset()
val p = unique_new(77, "once")
val p2 = unique_move(p)
expect(unique_get(p)).to_equal(-1)
unique_reset()
```

</details>

### Unique - into_inner

#### consumes and returns value

1. unique reset
   - Expected: v equals `33`
   - Expected: unique_is_valid(p) is false
2. unique reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unique_reset()
val p = unique_new(33, "consume")
val v = unique_into_inner(p)
expect(v).to_equal(33)
expect(unique_is_valid(p)).to_equal(false)
unique_reset()
```

</details>

### Unique - manual invalidate

#### marks as moved

1. unique reset
2. unique invalidate
   - Expected: unique_is_valid(p) is false
3. unique reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unique_reset()
val p = unique_new(55, "manual")
unique_invalidate(p.id)
expect(unique_is_valid(p)).to_equal(false)
unique_reset()
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
