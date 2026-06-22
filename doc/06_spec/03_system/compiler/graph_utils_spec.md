# Graph Utils Specification

> <details>

<!-- sdn-diagram:id=graph_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=graph_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

graph_utils_spec -> std
graph_utils_spec -> std_lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=graph_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Graph Utils Specification

## Scenarios

#### Create block ID

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an ID value"
val id = BlockId.new(5)
# When "getting the value"
val block_value = id.value()
# Then "it should be 5"
expect(block_value).to_equal(5)
```

</details>

#### Jump has one successor

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Jump terminator"
val term = Terminator.Jump(BlockId.new(10))
# When "getting successors"
val succs = term.successors()
# Then "it should have 1 successor"
expect(succs.length()).to_equal(1)
```

</details>

#### Branch has two successors

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Branch terminator"
val term = Terminator.Branch(BlockId.new(1), BlockId.new(2))
# When "getting successors"
val succs = term.successors()
# Then "it should have 2 successors"
expect(succs.length()).to_equal(2)
```

</details>

#### Return has no successors

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Return terminator"
val term = Terminator.Return
# When "getting successors"
val succs = term.successors()
# Then "it should have 0 successors"
expect(succs.length()).to_equal(0)
```

</details>

#### Return is terminal

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Return terminator"
val term = Terminator.Return
# When "checking if terminal"
val is_term = term.is_terminal()
# Then "it should be terminal"
expect(is_term).to_equal(true)
```

</details>

#### Jump is not terminal

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Jump terminator"
val term = Terminator.Jump(BlockId.new(1))
# When "checking if terminal"
val is_term = term.is_terminal()
# Then "it should not be terminal"
expect(is_term).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/graph_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
