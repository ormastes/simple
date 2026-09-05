# Simple Audio Offload Specification

> Tests covering pure-Simple audio offload reference.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Audio Offload Specification

## Scenarios

### pure-Simple audio offload reference

#### computes deterministic finite convolution

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- computes deterministic finite convolution
   - Expected: output equals `[0.5, 1.25, 0.5]`
   - Expected: simple_audio_convolve_reference([], [1.0]) equals `[]`
   - Expected: simple_audio_convolve_reference([1.0], []) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("computes deterministic finite convolution")
val output = simple_audio_convolve_reference([1.0, 2.0], [0.5, 0.25])
expect(output).to_equal([0.5, 1.25, 0.5])
expect(simple_audio_convolve_reference([], [1.0])).to_equal([])
expect(simple_audio_convolve_reference([1.0], [])).to_equal([])
```

</details>

#### measures exact and malformed candidate parity

- measures exact and malformed candidate parity
   - Expected: simple_audio_max_error_ppm([0.0, 1.0], [0.0, 1.0]) equals `0`
   - Expected: simple_audio_max_error_ppm([0.0], [0.0, 1.0]) equals `1000000`
   - Expected: check_spatial_audio_parity().max_sample_error_ppm equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("measures exact and malformed candidate parity")
expect(simple_audio_max_error_ppm([0.0, 1.0], [0.0, 1.0])).to_equal(0)
expect(simple_audio_max_error_ppm([0.0], [0.0, 1.0])).to_equal(1000000)
expect(check_spatial_audio_parity().max_sample_error_ppm).to_equal(0)
```

</details>

#### keeps callback and final output CPU owned

- keeps callback and final output CPU owned
   - Expected: result.callback_owned_by_cpu is true
   - Expected: result.final_output_owned_by_cpu is true
   - Expected: result.deadline_period_percent equals `60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps callback and final output CPU owned")
val result = check_audio_offload_fallback("vulkan")
expect(result.callback_owned_by_cpu).to_equal(true)
expect(result.final_output_owned_by_cpu).to_equal(true)
expect(result.deadline_period_percent).to_equal(60)
```

</details>

#### quarantines late work and returns every token on faults

- quarantines late work and returns every token on faults
   - Expected: result.timeout_fallback equals `cpu-next-period`
   - Expected: result.device_lost_fallback equals `cpu-next-period`
   - Expected: result.rejected_fallback equals `cpu-next-period`
   - Expected: result.queue_full_fallback equals `cpu-next-period`
   - Expected: result.output_gaps equals `0`
   - Expected: result.late_results_committed equals `0`
   - Expected: result.live_tokens equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("quarantines late work and returns every token on faults")
val result = check_audio_offload_fallback("faults")
expect(result.timeout_fallback).to_equal("cpu-next-period")
expect(result.device_lost_fallback).to_equal("cpu-next-period")
expect(result.rejected_fallback).to_equal("cpu-next-period")
expect(result.queue_full_fallback).to_equal("cpu-next-period")
expect(result.output_gaps).to_equal(0)
expect(result.late_results_committed).to_equal(0)
expect(result.live_tokens).to_equal(0)
```

</details>

#### reports unbound native capsules honestly

- reports unbound native capsules honestly
   - Expected: linux.status equals `unavailable`
   - Expected: linux.owner equals `pure-simple-contract`
   - Expected: wrong.status equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports unbound native capsules honestly")
val linux = check_simple_audio_backend("linux", "pipewire")
val wrong = check_simple_audio_backend("linux", "wasapi")
expect(linux.status).to_equal("unavailable")
expect(linux.owner).to_equal("pure-simple-contract")
expect(wrong.status).to_equal("unsupported")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/engine/audio/simple_audio_offload_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pure-Simple audio offload reference.
- pure-Simple audio offload reference

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
- `REQ-011`
- `REQ-012`
- `REQ-013`
- `REQ-014`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9131f10fdeb6477e304e26853ac05a35954d641d588e6852aa9c1855ec3685aa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9131f10fdeb6477e304e26853ac05a35954d641d588e6852aa9c1855ec3685aa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9131f10fdeb6477e304e26853ac05a35954d641d588e6852aa9c1855ec3685aa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/engine/audio/simple_audio_offload_spec.spl
mirror: doc/06_spec/01_unit/lib/common/engine/audio/simple_audio_offload_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/engine/audio/simple_audio_offload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/engine/audio/simple_audio_offload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/engine/audio/simple_audio_offload_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/engine/audio/simple_audio_offload_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/engine/audio/simple_audio_offload_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes deterministic finite convolution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/engine/audio/simple_audio_offload_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'measures exact and malformed candidate parity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/engine/audio/simple_audio_offload_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps callback and final output CPU owned' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
