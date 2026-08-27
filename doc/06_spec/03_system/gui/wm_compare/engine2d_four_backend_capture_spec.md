# Engine2d Four Backend Capture Specification

> Tests covering Engine2D four-backend capture contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Four Backend Capture Specification

## Scenarios

### Engine2D four-backend capture contract

#### REQ-E2D4-001/003/004 accepts complete deterministic evidence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- REQ-E2D4-001/003/004 accepts complete deterministic evidence
   - Expected: evidence.events.sequence equals `BACKEND_2D_EVENT_SEQUENCE`
   - Expected: backend_2d_validate_capture(evidence) equals `accepted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-E2D4-001/003/004 accepts complete deterministic evidence")
val evidence = valid_capture("metal")
expect(evidence.events.sequence).to_equal(BACKEND_2D_EVENT_SEQUENCE)
expect(backend_2d_validate_capture(evidence)).to_equal("accepted")
```

</details>

#### REQ-E2D4-003 rejects injection without target delivery

- REQ-E2D4-003 rejects injection without target delivery
   - Expected: backend_2d_validate_capture(evidence) equals `events_not_delivered`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-E2D4-003 rejects injection without target delivery")
val events = backend_2d_event_receipt("vulkan", true, false, "target_runtime")
val execution = backend_2d_execution_receipt(
    "device_readback", "device-1", false, 0, 0, false
)
val evidence = backend_2d_capture_evidence(
    "vulkan", "aarch64-apple-darwin", "engine2d-four-backend-v1",
    1200, 900, 300, hash_a(), "12,14,1180,870", events,
    "capture.ppm", "576be2a487", execution
)
expect(backend_2d_validate_capture(evidence)).to_equal("events_not_delivered")
```

</details>

#### REQ-E2D4-004 rejects self-reported evidence without a real hash

- REQ-E2D4-004 rejects self-reported evidence without a real hash
   - Expected: backend_2d_validate_capture(evidence) equals `invalid_pixel_sha256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-E2D4-004 rejects self-reported evidence without a real hash")
val events = backend_2d_event_receipt("cpu_simd", true, true, "target_runtime")
val execution = backend_2d_execution_receipt(
    "native_simd", "neon", false, 4, 2, true
)
val evidence = backend_2d_capture_evidence(
    "cpu_simd", "aarch64-apple-darwin", "engine2d-four-backend-v1",
    1200, 900, 300, "pass", "12,14,1180,870", events,
    "capture.ppm", "576be2a487", execution
)
expect(backend_2d_validate_capture(evidence)).to_equal("invalid_pixel_sha256")
```

</details>

#### REQ-E2D4-005 fails comparison when dimensions differ

- REQ-E2D4-005 fails comparison when dimensions differ
   - Expected: comparison.accepted is false
   - Expected: comparison.reason equals `dimension_mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-E2D4-005 fails comparison when dimensions differ")
val reference = valid_capture("cpu_simd")
val events = backend_2d_event_receipt(
    "simpleos_arm64_simd", true, true, "guest_virtio_input"
)
val execution = backend_2d_execution_receipt(
    "native_simd", "neon", false, 4, 2, true
)
val candidate = backend_2d_capture_evidence(
    "simpleos_arm64_simd", "aarch64-unknown-simpleos",
    "engine2d-four-backend-v1", 800, 600, 96, hash_a(),
    "12,14,780,570", events, "arm.ppm", "576be2a487", execution
)
val comparison = backend_2d_compare_capture(
    reference, candidate, 0, 0, "strict", false
)
expect(comparison.accepted).to_equal(false)
expect(comparison.reason).to_equal("dimension_mismatch")
```

</details>

#### REQ-E2D4-005 records exact-pixel equality independently of metadata acceptance

- REQ-E2D4-005 records exact-pixel equality independently of metadata acceptance
   - Expected: comparison.accepted is true
   - Expected: comparison.pixels_exact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-E2D4-005 records exact-pixel equality independently of metadata acceptance")
val reference = valid_capture("cpu_simd")
val candidate = valid_capture("vulkan")
val comparison = backend_2d_compare_capture(
    reference, candidate, 0, 0, "strict", false
)
expect(comparison.accepted).to_equal(true)
expect(comparison.pixels_exact).to_equal(true)
```

</details>

#### REQ-E2D4-005 requires an explicit pixel tolerance result for unequal hashes

- REQ-E2D4-005 requires an explicit pixel tolerance result for unequal hashes
   - Expected: rejected.reason equals `pixel_mismatch`
   - Expected: tolerated.accepted is true
   - Expected: tolerated.different_pixels equals `420`
   - Expected: tolerated.max_channel_diff equals `2`
   - Expected: tolerated.tolerance_profile equals `wm_default`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-E2D4-005 requires an explicit pixel tolerance result for unequal hashes")
val reference = valid_capture("cpu_simd")
val events = backend_2d_event_receipt("metal", true, true, "target_runtime")
val execution = backend_2d_execution_receipt(
    "device_readback", "device-1", false, 0, 0, false
)
val candidate = backend_2d_capture_evidence(
    "metal", "aarch64-apple-darwin", "engine2d-four-backend-v1",
    1200, 900, 300,
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
    "12,14,1180,870", events, "metal.ppm", "576be2a487", execution
)
val rejected = backend_2d_compare_capture(
    reference, candidate, 420, 2, "wm_default", false
)
val tolerated = backend_2d_compare_capture(
    reference, candidate, 420, 2, "wm_default", true
)
expect(rejected.reason).to_equal("pixel_mismatch")
expect(tolerated.accepted).to_equal(true)
expect(tolerated.different_pixels).to_equal(420)
expect(tolerated.max_channel_diff).to_equal(2)
expect(tolerated.tolerance_profile).to_equal("wm_default")
```

</details>

#### REQ-E2D4-002/006 rejects SIMD labels without execution counters

- REQ-E2D4-002/006 rejects SIMD labels without execution counters


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-E2D4-002/006 rejects SIMD labels without execution counters")
val events = backend_2d_event_receipt(
    "cpu_simd", true, true, "target_runtime"
)
val execution = backend_2d_execution_receipt(
    "native_simd", "neon", false, 0, 0, true
)
val evidence = backend_2d_capture_evidence(
    "cpu_simd", "aarch64-apple-darwin", "engine2d-four-backend-v1",
    1200, 900, 300, hash_a(), "12,14,1180,870", events,
    "capture.ppm", "576be2a487", execution
)
expect(backend_2d_validate_capture(evidence)).to_equal(
    "missing_simd_counters"
)
```

</details>

#### REQ-E2D4-002/006 rejects GPU evidence using a CPU mirror

- REQ-E2D4-002/006 rejects GPU evidence using a CPU mirror


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-E2D4-002/006 rejects GPU evidence using a CPU mirror")
val events = backend_2d_event_receipt(
    "vulkan", true, true, "target_runtime"
)
val execution = backend_2d_execution_receipt(
    "device_readback", "device-1", true, 0, 0, false
)
val evidence = backend_2d_capture_evidence(
    "vulkan", "aarch64-apple-darwin", "engine2d-four-backend-v1",
    1200, 900, 300, hash_a(), "12,14,1180,870", events,
    "capture.ppm", "576be2a487", execution
)
expect(backend_2d_validate_capture(evidence)).to_equal(
    "cpu_fallback_used"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/engine2d_four_backend_capture_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D four-backend capture contract.
- Engine2D four-backend capture contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1214cd96a20a5d9abb98c2805c99f0850774eb1fa226eec4c79f5d34991d08cd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1214cd96a20a5d9abb98c2805c99f0850774eb1fa226eec4c79f5d34991d08cd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1214cd96a20a5d9abb98c2805c99f0850774eb1fa226eec4c79f5d34991d08cd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/gui/wm_compare/engine2d_four_backend_capture_spec.spl
mirror: doc/06_spec/03_system/gui/wm_compare/engine2d_four_backend_capture_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/wm_compare/engine2d_four_backend_capture_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_compare/engine2d_four_backend_capture_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_compare/engine2d_four_backend_capture_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/wm_compare/engine2d_four_backend_capture_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-E2D4-001/003/004 accepts complete deterministic evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/engine2d_four_backend_capture_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-E2D4-005 records exact-pixel equality independently of metadata acceptance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
