# Loop Detect Specification

> Tests covering MIR natural loop detection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Loop Detect Specification

## Scenarios

### MIR natural loop detection

#### includes predecessors between the header and backedge source

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val func = loop_test_function()
var canonical_detector = LoopDetector.new()
canonical_detector.detect_loops(func)
val loops = canonical_detector.loops

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

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var canonical_detector = LoopDetector.new()
canonical_detector.detect_loops(loop_self_function())
val loops = canonical_detector.loops

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

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var canonical_detector = LoopDetector.new()
canonical_detector.detect_loops(loop_shared_exit_function())
val loops = canonical_detector.loops

expect(loops.len()).to_equal(1)
val loop_info: LoopInfo = loops[0]
expect(loop_info.exit_edges.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/compiler/mir/loop_detect_spec.spl` |
| Updated | 2026-10-09 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR natural loop detection.
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
