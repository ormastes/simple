# Backend Opencl Text Fallback Specification

> Tests covering Engine2D OpenCL text fallback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Opencl Text Fallback Specification

## Scenarios

### Engine2D OpenCL text fallback

#### uses mirror draw_text without staging a device glyph upload when unavailable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses mirror draw_text without staging a device glyph upload when unavailable
   - Expected: backend.mirror.init(8, 8) is true
   - Expected: backend.device_current is false
   - Expected: pixels.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses mirror draw_text without staging a device glyph upload when unavailable")
var backend = OpenClBackend.create()
expect(backend.mirror.init(8, 8)).to_equal(true)

backend.device_current = true
backend.draw_text(0, 0, "A", 0xff112233u32, 7)

val pixels = backend.read_pixels()
expect(backend.device_current).to_equal(false)
expect(pixels.len()).to_equal(64)

backend.shutdown()
```

</details>

#### uses mirror draw_text_bg without staging a device glyph upload when unavailable

- uses mirror draw_text_bg without staging a device glyph upload when unavailable
   - Expected: backend.mirror.init(8, 8) is true
   - Expected: backend.device_current is false
   - Expected: pixels.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses mirror draw_text_bg without staging a device glyph upload when unavailable")
var backend = OpenClBackend.create()
expect(backend.mirror.init(8, 8)).to_equal(true)

backend.device_current = true
backend.draw_text_bg(0, 0, "A", 0xff112233u32, 0xff445566u32, 7)

val pixels = backend.read_pixels()
expect(backend.device_current).to_equal(false)
expect(pixels.len()).to_equal(64)

backend.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/backend_opencl_text_fallback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D OpenCL text fallback.
- Engine2D OpenCL text fallback

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6a6cc49fcb07aacce2a96791d8884163be1e3a53ed7f6e9dd0240a129182e8b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6a6cc49fcb07aacce2a96791d8884163be1e3a53ed7f6e9dd0240a129182e8b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6a6cc49fcb07aacce2a96791d8884163be1e3a53ed7f6e9dd0240a129182e8b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gpu/engine2d/backend_opencl_text_fallback_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/backend_opencl_text_fallback_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/backend_opencl_text_fallback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/backend_opencl_text_fallback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/backend_opencl_text_fallback_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gpu/engine2d/backend_opencl_text_fallback_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses mirror draw_text without staging a device glyph upload when unavailable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/backend_opencl_text_fallback_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses mirror draw_text_bg without staging a device glyph upload when unavailable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
