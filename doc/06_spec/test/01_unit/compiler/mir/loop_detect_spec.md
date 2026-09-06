# Loop Detect Specification

> <details>

<!-- sdn-diagram:id=loop_detect_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=loop_detect_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

loop_detect_spec -> std
loop_detect_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=loop_detect_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Loop Detect Specification

## Scenarios

### MIR natural loop detection

#### includes predecessors between the header and backedge source

- var detector = LoopDetector new
- detector detect loops
   - Expected: detector.loops.len() equals `1`
   - Expected: receiver_loop.contains_block(BlockId.new(2)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val func = loop_test_function()
val loops = loop_detector_detect_loops(func)

expect(loops.len()).to_equal(1)
val loop_info: LoopInfo = loops[0]
expect(loop_info.backedges.len()).to_equal(1)
val backedge: BlockId = loop_info.backedges[0]
expect(backedge.id).to_equal(3)
expect(loop_info.body.len()).to_equal(2)
expect(loop_info.contains_block(BlockId.new(2))).to_equal(true)
expect(loop_info.contains_block(BlockId.new(3))).to_equal(true)

var detector = LoopDetector.new()
detector.detect_loops(func)
expect(detector.loops.len()).to_equal(1)
val receiver_loop: LoopInfo = detector.loops[0]
expect(receiver_loop.contains_block(BlockId.new(2))).to_equal(true)
```

</details>

<details>
<summary>Advanced: retains a self-loop backedge without duplicating its header in the body</summary>

#### retains a self-loop backedge without duplicating its header in the body

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loops = loop_detector_detect_loops(loop_self_function())

expect(loops.len()).to_equal(1)
val loop_info: LoopInfo = loops[0]
expect(loop_info.backedges.len()).to_equal(1)
val backedge: BlockId = loop_info.backedges[0]
expect(backedge.id).to_equal(0)
expect(loop_info.body.len()).to_equal(0)
```

</details>


</details>

#### keeps distinct exit edges that share a destination

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loops = loop_detector_detect_loops(loop_shared_exit_function())

expect(loops.len()).to_equal(1)
val loop_info: LoopInfo = loops[0]
expect(loop_info.exit_edges.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/loop_detect_spec.spl` |
| Updated | 2026-07-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MIR natural loop detection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
