# metal_lane_session_spec

> Host-aware coverage for the Metal lane session shell's probe path: on

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# metal_lane_session_spec

Host-aware coverage for the Metal lane session shell's probe path: on

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/gpu_lane/metal_lane_session_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Host-aware coverage for the Metal lane session shell's probe path: on
    this Linux dev host (no macOS/Metal), `probe()` must return a
    `skip:metal-unavailable-not-macos` result -- never a crash, hang, or
    silent pass -- proving the probe contract itself works correctly ahead
    of real Mac hardware verification.

## Scenarios

### MetalLaneSession host-aware probe

#### should probe cleanly and report the macOS-absence skip reason on this host

- should probe cleanly and report the macOS-absence skip reason on this host
- Probe for a Metal-capable device
- metal
   - Expected: probe_result equals `skip:metal-unavailable-not-macos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should probe cleanly and report the macOS-absence skip reason on this host")
step("Probe for a Metal-capable device")
var session = MetalLaneSession.create()
val probe_result = session.probe()

# Fail closed -- see lane_probe_verdict.spl. The old
# `assert_true(probe_result.starts_with("skip:"))` passed BECAUSE the
# probe skipped: on a macOS host with a real Metal device this example
# would have gone on reporting a green "clean skip" forever.
step(gpu_lane_probe_verdict_reason("metal", probe_result))
gpu_lane_report_skip("metal lane", probe_result)
assert_equal(gpu_lane_probe_verdict("metal", probe_result), "skip")
expect(probe_result).to_equal("skip:metal-unavailable-not-macos")
```

</details>

#### should refuse init() before a live device is available, returning the same skip reason

- should refuse init() before a live device is available, returning the same skip reason
- Attempt init() directly against an unprobed session
- init() must route through probe() and report the same skip, not raise or hang
   - Expected: init_result equals `skip:metal-unavailable-not-macos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should refuse init() before a live device is available, returning the same skip reason")
step("Attempt init() directly against an unprobed session")
var session = MetalLaneSession.create()
val init_result = session.init(4096, "kernel void lane_main() {}", "lane_main")

step("init() must route through probe() and report the same skip, not raise or hang")
assert_true(init_result.starts_with("skip:"))
expect(init_result).to_equal("skip:metal-unavailable-not-macos")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c0f1740554c9aa0f47834012c52d0fd22a9a6408dd47f16abf90a09e043e7798`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c0f1740554c9aa0f47834012c52d0fd22a9a6408dd47f16abf90a09e043e7798`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c0f1740554c9aa0f47834012c52d0fd22a9a6408dd47f16abf90a09e043e7798`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/gpu_lane/metal_lane_session_spec.spl
mirror: doc/06_spec/02_integration/gpu_lane/metal_lane_session_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/gpu_lane/metal_lane_session_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/gpu_lane/metal_lane_session_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/gpu_lane/metal_lane_session_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should probe cleanly and report the macOS-absence skip reason on this host' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/gpu_lane/metal_lane_session_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should probe cleanly and report the macOS-absence skip reason on this host' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/gpu_lane/metal_lane_session_spec.spl:50:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should refuse init() before a live device is available, returning the same skip reason' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/gpu_lane/metal_lane_session_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should refuse init() before a live device is available, returning the same skip reason' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
