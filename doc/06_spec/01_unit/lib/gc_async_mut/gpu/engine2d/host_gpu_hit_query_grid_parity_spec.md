# Host Gpu Hit Query Grid Parity Specification

> Tests covering Stage A hit_stack resolver vs Stage B grid resolver -- CPU parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Gpu Hit Query Grid Parity Specification

## Scenarios

### Stage A hit_stack resolver vs Stage B grid resolver -- CPU parity

#### agree on a hit at a known point

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- agree on a hit at a known point


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agree on a hit at a known point")
val comp = _sample_composition()
val forest = draw_ir_hit_forest(comp)
val grid = simple_2d_hit_grid_rasterize(forest.proxies, GRID_W, GRID_H)
val packet = engine2d_host_gpu_hit_query_packet("evt-hit", 120, 120, 3)

val cpu_readback = engine2d_host_gpu_hit_query_resolve_cpu(packet, forest)
val grid_readback = engine2d_host_gpu_hit_query_resolve_grid(packet, grid)

assert_true(cpu_readback.hit)
assert_true(grid_readback.hit)
assert_equal(grid_readback.node_id, cpu_readback.node_id)
assert_equal(grid_readback.node_id, draw_ir_node_id("panel.button"))
```

</details>

#### agree on the miss sentinel when the point hits nothing

- agree on the miss sentinel when the point hits nothing


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agree on the miss sentinel when the point hits nothing")
val comp = _sample_composition()
val forest = draw_ir_hit_forest(comp)
val grid = simple_2d_hit_grid_rasterize(forest.proxies, GRID_W, GRID_H)
val packet = engine2d_host_gpu_hit_query_packet("evt-miss", 5, 5, 3)

val cpu_readback = engine2d_host_gpu_hit_query_resolve_cpu(packet, forest)
val grid_readback = engine2d_host_gpu_hit_query_resolve_grid(packet, grid)

assert_false(cpu_readback.hit)
assert_false(grid_readback.hit)
assert_equal(grid_readback.node_id, ENGINE2D_HOST_GPU_HIT_QUERY_MISS)
assert_equal(grid_readback.node_id, cpu_readback.node_id)
```

</details>

#### agree on the topmost-by-layer winner for overlapping proxies

- agree on the topmost-by-layer winner for overlapping proxies


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agree on the topmost-by-layer winner for overlapping proxies")
val comp = _overlap_composition()
val forest = draw_ir_hit_forest(comp)
val grid = simple_2d_hit_grid_rasterize(forest.proxies, GRID_W, GRID_H)
val packet = engine2d_host_gpu_hit_query_packet("evt-overlap", 50, 50, 1)

val cpu_readback = engine2d_host_gpu_hit_query_resolve_cpu(packet, forest)
val grid_readback = engine2d_host_gpu_hit_query_resolve_grid(packet, grid)

assert_true(cpu_readback.hit)
assert_true(grid_readback.hit)
assert_equal(cpu_readback.node_id, draw_ir_node_id("high.panel"))
assert_equal(grid_readback.node_id, cpu_readback.node_id)
```

</details>

#### agree on a miss point that is inside the grid but outside every proxy

- agree on a miss point that is inside the grid but outside every proxy


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agree on a miss point that is inside the grid but outside every proxy")
val comp = _overlap_composition()
val forest = draw_ir_hit_forest(comp)
val grid = simple_2d_hit_grid_rasterize(forest.proxies, GRID_W, GRID_H)
val packet = engine2d_host_gpu_hit_query_packet("evt-inside-grid-miss", 150, 150, 1)

val cpu_readback = engine2d_host_gpu_hit_query_resolve_cpu(packet, forest)
val grid_readback = engine2d_host_gpu_hit_query_resolve_grid(packet, grid)

assert_false(cpu_readback.hit)
assert_false(grid_readback.hit)
assert_equal(grid_readback.node_id, cpu_readback.node_id)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/host_gpu_hit_query_grid_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Stage A hit_stack resolver vs Stage B grid resolver -- CPU parity.
- Stage A hit_stack resolver vs Stage B grid resolver -- CPU parity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0a82c3d439960c191b0d3bc3ea6090a2384827433a7f90daad165fbbdbe557f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0a82c3d439960c191b0d3bc3ea6090a2384827433a7f90daad165fbbdbe557f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0a82c3d439960c191b0d3bc3ea6090a2384827433a7f90daad165fbbdbe557f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/host_gpu_hit_query_grid_parity_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/host_gpu_hit_query_grid_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/host_gpu_hit_query_grid_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/host_gpu_hit_query_grid_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/host_gpu_hit_query_grid_parity_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agree on a hit at a known point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/host_gpu_hit_query_grid_parity_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agree on the miss sentinel when the point hits nothing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/host_gpu_hit_query_grid_parity_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agree on the topmost-by-layer winner for overlapping proxies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
