# Simple Audio Contract Specification

> Tests covering pure-Simple audio graph contracts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Audio Contract Specification

## Scenarios

### pure-Simple audio graph contracts

#### validates format boundaries

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- validates format boundaries
   - Expected: simple_audio_format_status(SimpleAudioFormat(sample_rate: 8000, channels: 1, period_frames: 16, sample_kind: "i16")) equals `accepted`
   - Expected: simple_audio_format_status(SimpleAudioFormat(sample_rate: 384000, channels: 16, period_frames: 8192, sample_kind: "f32")) equals `accepted`
   - Expected: simple_audio_format_status(SimpleAudioFormat(sample_rate: 7999, channels: 2, period_frames: 256, sample_kind: "f32")) equals `invalid-format`
   - Expected: simple_audio_format_status(SimpleAudioFormat(sample_rate: 48000, channels: 0, period_frames: 256, sample_kind: "f32")) equals `invalid-format`
   - Expected: simple_audio_format_status(SimpleAudioFormat(sample_rate: 48000, channels: 2, period_frames: 8, sample_kind: "f32")) equals `invalid-format`
   - Expected: simple_audio_format_status(SimpleAudioFormat(sample_rate: 48000, channels: 2, period_frames: 256, sample_kind: "bad")) equals `invalid-format`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("validates format boundaries")
expect(simple_audio_format_status(SimpleAudioFormat(sample_rate: 8000, channels: 1, period_frames: 16, sample_kind: "i16"))).to_equal("accepted")
expect(simple_audio_format_status(SimpleAudioFormat(sample_rate: 384000, channels: 16, period_frames: 8192, sample_kind: "f32"))).to_equal("accepted")
expect(simple_audio_format_status(SimpleAudioFormat(sample_rate: 7999, channels: 2, period_frames: 256, sample_kind: "f32"))).to_equal("invalid-format")
expect(simple_audio_format_status(SimpleAudioFormat(sample_rate: 48000, channels: 0, period_frames: 256, sample_kind: "f32"))).to_equal("invalid-format")
expect(simple_audio_format_status(SimpleAudioFormat(sample_rate: 48000, channels: 2, period_frames: 8, sample_kind: "f32"))).to_equal("invalid-format")
expect(simple_audio_format_status(SimpleAudioFormat(sample_rate: 48000, channels: 2, period_frames: 256, sample_kind: "bad"))).to_equal("invalid-format")
```

</details>

#### clamps deterministic pan endpoints

- clamps deterministic pan endpoints
   - Expected: simple_audio_equal_power_pan_milli(-2000) equals `(1000, 0)`
   - Expected: simple_audio_equal_power_pan_milli(0) equals `(500, 500)`
   - Expected: simple_audio_equal_power_pan_milli(2000) equals `(0, 1000)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clamps deterministic pan endpoints")
expect(simple_audio_equal_power_pan_milli(-2000)).to_equal((1000, 0))
expect(simple_audio_equal_power_pan_milli(0)).to_equal((500, 500))
expect(simple_audio_equal_power_pan_milli(2000)).to_equal((0, 1000))
```

</details>

#### renders one shared direct 2D and 3D epoch

- renders one shared direct 2D and 3D epoch
   - Expected: result.direct_status equals `rendered`
   - Expected: result.engine2d_status equals `rendered`
   - Expected: result.engine3d_status equals `rendered`
   - Expected: result.graph_epoch_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders one shared direct 2D and 3D epoch")
val result = simple_audio_graph_operator_probe("direct-2d-3d")
expect(result.direct_status).to_equal("rendered")
expect(result.engine2d_status).to_equal("rendered")
expect(result.engine3d_status).to_equal("rendered")
expect(result.graph_epoch_count).to_equal(1)
```

</details>

#### reports lifecycle faults and releases resources

- reports lifecycle faults and releases resources
   - Expected: faults.queue_full equals `queue-full`
   - Expected: faults.post_shutdown_events equals `0`
   - Expected: resources.stale_generation_status equals `stale-generation`
   - Expected: resources.live_handles equals `0`
   - Expected: resources.live_mappings equals `0`
   - Expected: resources.live_buffers equals `0`
   - Expected: resources.live_callbacks equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports lifecycle faults and releases resources")
val faults = simple_audio_graph_fault_probe()
val resources = simple_audio_graph_resource_probe()
expect(faults.queue_full).to_equal("queue-full")
expect(faults.post_shutdown_events).to_equal(0)
expect(resources.stale_generation_status).to_equal("stale-generation")
expect(resources.live_handles).to_equal(0)
expect(resources.live_mappings).to_equal(0)
expect(resources.live_buffers).to_equal(0)
expect(resources.live_callbacks).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/engine/audio/simple_audio_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pure-Simple audio graph contracts.
- pure-Simple audio graph contracts

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
- `REQ-007`
- `REQ-008`
- `REQ-009`
- `REQ-016`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `082fffc2143f828b5ee1f9351034d909530ea6999cf8e5304af1350c143c56b0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `082fffc2143f828b5ee1f9351034d909530ea6999cf8e5304af1350c143c56b0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `082fffc2143f828b5ee1f9351034d909530ea6999cf8e5304af1350c143c56b0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/engine/audio/simple_audio_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/common/engine/audio/simple_audio_contract_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/engine/audio/simple_audio_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/engine/audio/simple_audio_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/engine/audio/simple_audio_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/engine/audio/simple_audio_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/engine/audio/simple_audio_contract_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates format boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/engine/audio/simple_audio_contract_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clamps deterministic pan endpoints' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/engine/audio/simple_audio_contract_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders one shared direct 2D and 3D epoch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
