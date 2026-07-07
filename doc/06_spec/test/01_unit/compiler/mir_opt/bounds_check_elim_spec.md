# BoundsCheckElimination Specification

> Validates the BoundsCheckElimination pass which removes redundant `bounds_check` intrinsic calls using same-block deduplication and loop-bounds proofs.

<!-- sdn-diagram:id=bounds_check_elim_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bounds_check_elim_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bounds_check_elim_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bounds_check_elim_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BoundsCheckElimination Specification

Validates the BoundsCheckElimination pass which removes redundant `bounds_check` intrinsic calls using same-block deduplication and loop-bounds proofs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #web-server-optimizer-complete |
| Category | Compiler / MIR Optimization |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/compiler/mir_opt/bounds_check_elim_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the BoundsCheckElimination pass which removes redundant
`bounds_check` intrinsic calls using same-block deduplication and
loop-bounds proofs.

## Behavior

- Duplicate bounds check on same index+length in same block is eliminated
- Bounds check on a different index is preserved
- Bounds check inside a loop with a proven-safe loop bound is eliminated
- Pass statistics count every eliminated check

## Scenarios

### BoundsCheckElimination

### same-block deduplication

#### elides redundant bounds check dominated by earlier check on same index

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Two checks with identical index=%idx len=%len in the same block.
val key = make_bounds_check_key("%idx", "%len")
val checks_in_block = [key, key]
val kept = simulate_block_dedup(checks_in_block)
# Only the first check should survive.
expect(kept.len()).to_equal(1)
expect(kept[0]).to_equal(key)
```

</details>

#### preserves bounds check when index differs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key_a = make_bounds_check_key("%idx0", "%len")
val key_b = make_bounds_check_key("%idx1", "%len")
val checks_in_block = [key_a, key_b]
val kept = simulate_block_dedup(checks_in_block)
# Both have distinct keys — both must be preserved.
expect(kept.len()).to_equal(2)
```

</details>

### loop-bounds proof

<details>
<summary>Advanced: elides bounds check inside loop when loop bound proven safe</summary>

#### elides bounds check inside loop when loop bound proven safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Loop runs 0..8, array length is 16 — provably safe.
val loop_bound = 8
val array_len = 16
val safe = simulate_loop_bounds_proof(loop_bound, array_len)
expect(safe).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: does not elide bounds check when loop bound exceeds array length</summary>

#### does not elide bounds check when loop bound exceeds array length

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Loop runs 0..20, array length is 16 — NOT proven safe.
val loop_bound = 20
val array_len = 16
val safe = simulate_loop_bounds_proof(loop_bound, array_len)
expect(safe).to_equal(false)
```

</details>


</details>

### intrinsic name recognition

#### recognises all four bounds_check intrinsic name variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = ["bounds_check", "array_bounds_check", "rt_bounds_check", "__simple_bounds_check"]
var i = 0
while i < names.len():
    val recognised = is_bounds_check_intrinsic(names[i])
    expect(recognised).to_equal(true)
    i = i + 1
```

</details>

#### does not recognise unrelated intrinsic names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val recognised = is_bounds_check_intrinsic("memcpy")
expect(recognised).to_equal(false)
```

</details>

### pass statistics

#### counts eliminated checks in pass statistics

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Block had 4 checks; after dedup 2 remain → 2 eliminated.
val key_a = make_bounds_check_key("%idx", "%len")
val key_b = make_bounds_check_key("%idx2", "%len")
val checks = [key_a, key_a, key_b, key_b]
val kept = simulate_block_dedup(checks)
val eliminated = simulate_pass_stats(checks.len(), kept.len())
expect(eliminated).to_equal(2)
expect(eliminated).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
