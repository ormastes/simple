# Ik Solver Specification

> 1. var chain = IKChain new

<!-- sdn-diagram:id=ik_solver_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ik_solver_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ik_solver_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ik_solver_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ik Solver Specification

## Scenarios

### IKChain

#### creates empty chain

1. var chain = IKChain new
   - Expected: chain.joint_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var chain = IKChain.new(0.01, 10)
expect(chain.joint_count()).to_equal(0)
```

</details>

#### adds joints

1. var chain = IKChain new
2. chain add joint
3. chain add joint
4. chain add joint
   - Expected: chain.joint_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var chain = IKChain.new(0.01, 10)
chain.add_joint(0.0, 0.0, 1.0)
chain.add_joint(1.0, 0.0, 1.0)
chain.add_joint(2.0, 0.0, 0.0)
expect(chain.joint_count()).to_equal(3)
```

</details>

#### computes total chain length

1. var chain = IKChain new
2. chain add joint
3. chain add joint
4. chain add joint
   - Expected: chain.total_chain_length() equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var chain = IKChain.new(0.01, 10)
chain.add_joint(0.0, 0.0, 2.0)
chain.add_joint(2.0, 0.0, 3.0)
chain.add_joint(5.0, 0.0, 0.0)
expect(chain.total_chain_length()).to_equal(5.0)
```

</details>

#### returns end effector position

1. var chain = IKChain new
2. chain add joint
3. chain add joint
4. chain add joint
   - Expected: chain.end_effector_x() equals `2.0`
   - Expected: chain.end_effector_y() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var chain = IKChain.new(0.01, 10)
chain.add_joint(0.0, 0.0, 1.0)
chain.add_joint(1.0, 0.0, 1.0)
chain.add_joint(2.0, 0.0, 0.0)
expect(chain.end_effector_x()).to_equal(2.0)
expect(chain.end_effector_y()).to_equal(0.0)
```

</details>

#### solves reachable target

1. var chain = IKChain new
2. chain add joint
3. chain add joint
4. chain add joint


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var chain = IKChain.new(0.1, 20)
chain.add_joint(0.0, 0.0, 1.0)
chain.add_joint(1.0, 0.0, 1.0)
chain.add_joint(2.0, 0.0, 0.0)
val ok = chain.solve(1.5, 1.0)
# End effector should be near target
val ex = chain.end_effector_x()
val ey = chain.end_effector_y()
expect(ex).to_be_greater_than(1.0)
expect(ey).to_be_greater_than(0.5)
```

</details>

#### returns false for unreachable target

1. var chain = IKChain new
2. chain add joint
3. chain add joint
4. chain add joint
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var chain = IKChain.new(0.01, 10)
chain.add_joint(0.0, 0.0, 1.0)
chain.add_joint(1.0, 0.0, 1.0)
chain.add_joint(2.0, 0.0, 0.0)
val ok = chain.solve(100.0, 0.0)
expect(ok).to_equal(false)
```

</details>

#### preserves root position after solve

1. var chain = IKChain new
2. chain add joint
3. chain add joint
4. chain add joint
5. chain solve
   - Expected: root.x equals `0.0`
   - Expected: root.y equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var chain = IKChain.new(0.1, 20)
chain.add_joint(0.0, 0.0, 1.0)
chain.add_joint(1.0, 0.0, 1.0)
chain.add_joint(2.0, 0.0, 0.0)
chain.solve(1.5, 1.0)
if val Some(root) = chain.get_joint(0):
    expect(root.x).to_equal(0.0)
    expect(root.y).to_equal(0.0)
```

</details>

#### returns false for chain with less than 2 joints

1. var chain = IKChain new
2. chain add joint
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var chain = IKChain.new(0.01, 10)
chain.add_joint(0.0, 0.0, 1.0)
val ok = chain.solve(1.0, 0.0)
expect(ok).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/ik_solver_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- IKChain

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
