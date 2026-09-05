# Host Gpu Hit Query Specification

> Tests covering Engine2D GPU offload Stage A: hit query packet + readback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Gpu Hit Query Specification

## Scenarios

### Engine2D GPU offload Stage A: hit query packet + readback

#### round-trips a hit-query packet through its wire payload text

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips a hit-query packet through its wire payload text


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a hit-query packet through its wire payload text")
val packet = engine2d_host_gpu_hit_query_packet("evt-1", 120, 130, 7)
val payload_text = engine2d_host_gpu_hit_query_payload_text(packet)
val decoded = engine2d_host_gpu_hit_query_packet_from_payload_text(payload_text)

assert_equal(decoded.event_id, "evt-1")
assert_equal(decoded.x, 120)
assert_equal(decoded.y, 130)
assert_equal(decoded.generation, 7)
```

</details>

#### resolves a hit at a known point to the expected DrawIR node id

- resolves a hit at a known point to the expected DrawIR node id


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a hit at a known point to the expected DrawIR node id")
val comp = _sample_composition()
val forest = draw_ir_hit_forest(comp)
val expected_node_id = draw_ir_node_id("panel.button")
val packet = engine2d_host_gpu_hit_query_packet("evt-hit", 120, 120, 3)

val readback = engine2d_host_gpu_hit_query_resolve_cpu(packet, forest)

assert_true(readback.hit)
assert_equal(readback.node_id, expected_node_id)
assert_equal(readback.generation, 3)
```

</details>

#### returns the miss sentinel when the point hits nothing

- returns the miss sentinel when the point hits nothing


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the miss sentinel when the point hits nothing")
val comp = _sample_composition()
val forest = draw_ir_hit_forest(comp)
val packet = engine2d_host_gpu_hit_query_packet("evt-miss", 5, 5, 3)

val readback = engine2d_host_gpu_hit_query_resolve_cpu(packet, forest)

assert_false(readback.hit)
assert_equal(readback.node_id, ENGINE2D_HOST_GPU_HIT_QUERY_MISS)
```

</details>

#### discards a stale-generation readback instead of returning it as a hit

- discards a stale-generation readback instead of returning it as a hit


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("discards a stale-generation readback instead of returning it as a hit")
val comp = _sample_composition()
val forest = draw_ir_hit_forest(comp)
val expected_node_id = draw_ir_node_id("panel.button")
val packet = engine2d_host_gpu_hit_query_packet("evt-stale", 120, 120, 3)
val readback = engine2d_host_gpu_hit_query_resolve_cpu(packet, forest)

val fresh = engine2d_host_gpu_hit_query_apply_readback(3, readback)
val stale = engine2d_host_gpu_hit_query_apply_readback(4, readback)

assert_true(fresh.hit)
assert_equal(fresh.node_id, expected_node_id)
assert_false(stale.hit)
assert_equal(stale.node_id, ENGINE2D_HOST_GPU_HIT_QUERY_MISS)
```

</details>

#### admits the hit-query operation through the host/gpu lane scheduler

- admits the hit-query operation through the host/gpu lane scheduler


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits the hit-query operation through the host/gpu lane scheduler")
val packet = engine2d_host_gpu_hit_query_packet("evt-lane", 120, 120, 3)
val payload_text = engine2d_host_gpu_hit_query_payload_text(packet)
val packet_bytes = payload_text.len().to_i64()

val result = engine2d_host_gpu_lane_schedule(
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "hit_query",
    packet_bytes,
    512,
    false,
    false,
    true,
    1
)

assert_true(result.ok)
assert_true(result.gpu_batched)
assert_equal(result.execution_kind, ENGINE2D_HOST_GPU_EXEC_PACKET)
```

</details>

#### still rejects per-widget dispatch and host-semantic mutation for hit queries

- still rejects per-widget dispatch and host-semantic mutation for hit queries


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still rejects per-widget dispatch and host-semantic mutation for hit queries")
val per_widget = engine2d_host_gpu_lane_schedule(
    ENGINE2D_HOST_GPU_LANE_HOST, ENGINE2D_HOST_GPU_LANE_GPU,
    "hit_query", 32, 512, false, true, true, 1
)
val mutating = engine2d_host_gpu_lane_schedule(
    ENGINE2D_HOST_GPU_LANE_HOST, ENGINE2D_HOST_GPU_LANE_GPU,
    "hit_query", 32, 512, true, false, true, 1
)

assert_false(per_widget.ok)
assert_false(mutating.ok)
```

</details>

#### exposes the hit-query packet kind alongside the Draw IR kind

- exposes the hit-query packet kind alongside the Draw IR kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes the hit-query packet kind alongside the Draw IR kind")
assert_equal(ENGINE2D_HOST_GPU_RUNTIME_KIND_HIT_QUERY, 2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/host_gpu_hit_query_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D GPU offload Stage A: hit query packet + readback.
- Engine2D GPU offload Stage A: hit query packet + readback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `dba0de6ac0af22ebb51a3802a57dbec58209da5d182cf27d661f7771018b614e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dba0de6ac0af22ebb51a3802a57dbec58209da5d182cf27d661f7771018b614e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dba0de6ac0af22ebb51a3802a57dbec58209da5d182cf27d661f7771018b614e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/host_gpu_hit_query_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/host_gpu_hit_query_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/host_gpu_hit_query_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/host_gpu_hit_query_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/host_gpu_hit_query_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a hit-query packet through its wire payload text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/host_gpu_hit_query_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a hit at a known point to the expected DrawIR node id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/host_gpu_hit_query_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the miss sentinel when the point hits nothing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
