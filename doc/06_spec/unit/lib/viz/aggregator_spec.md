# Aggregator Specification

> Tests covering Aggregator.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aggregator Specification

## Scenarios

### Aggregator

#### new Aggregator has 0 known_frames

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- new Aggregator has 0 known_frames


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new Aggregator has 0 known_frames")
val agg = Aggregator.new()
expect agg.known_frames.len() to_equal 0
```

</details>

#### register_frame adds one entry

- register_frame adds one entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("register_frame adds one entry")
var agg = Aggregator.new()
val sid = _sid(1, 2, 0, 1)
val entry = AggregatorEntry(surface_id: sid, frame: CompositorFrame.empty())
agg.register_frame(entry)
expect agg.known_frames.len() to_equal 1
```

</details>

#### register_frame with duplicate SurfaceId replaces, size stays 1

- register_frame with duplicate SurfaceId replaces, size stays 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("register_frame with duplicate SurfaceId replaces, size stays 1")
var agg = Aggregator.new()
val sid = _sid(1, 2, 0, 1)
val entry1 = AggregatorEntry(surface_id: sid, frame: _frame_with_passes(1))
val entry2 = AggregatorEntry(surface_id: sid, frame: _frame_with_passes(3))
agg.register_frame(entry1)
agg.register_frame(entry2)
expect agg.known_frames.len() to_equal 1
```

</details>

#### aggregate with unknown root returns empty frame

- aggregate with unknown root returns empty frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aggregate with unknown root returns empty frame")
var agg = Aggregator.new()
val unknown = _sid(99, 99, 0, 0)
val result = agg.aggregate(unknown)
expect result.render_pass_list.len() to_equal 0
```

</details>

#### aggregate with known root returns that frame's pass count

- aggregate with known root returns that frame's pass count


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aggregate with known root returns that frame's pass count")
var agg = Aggregator.new()
val sid = _sid(1, 1, 0, 1)
val entry = AggregatorEntry(surface_id: sid, frame: _frame_with_passes(2))
agg.register_frame(entry)
val result = agg.aggregate(sid)
expect result.render_pass_list.len() to_equal 2
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/viz/aggregator_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Aggregator.
- Aggregator

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `c65107b28957ca19828516e1f9bc7adc218de6439e450ec0f861a007bd5c5695`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c65107b28957ca19828516e1f9bc7adc218de6439e450ec0f861a007bd5c5695`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c65107b28957ca19828516e1f9bc7adc218de6439e450ec0f861a007bd5c5695`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/viz/aggregator_spec.spl
mirror: doc/06_spec/unit/lib/viz/aggregator_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/viz/aggregator_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/viz/aggregator_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/viz/aggregator_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'new Aggregator has 0 known_frames' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/viz/aggregator_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'register_frame adds one entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/viz/aggregator_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'register_frame with duplicate SurfaceId replaces, size stays 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
