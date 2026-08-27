# webgpu_status_errors_spec

> Purpose: Verify Browser WebGPU status and errors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# webgpu_status_errors_spec

Purpose: Verify Browser WebGPU status and errors.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/web_platform/webgpu/webgpu_status_errors_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify Browser WebGPU status and errors.
Audience: QA and feature maintainers reading this spec suite.

## Scenarios

### Browser WebGPU status and errors

### error scopes

#### captures the first matching validation error in a pushed scope

- captures the first matching validation error in a pushed scope
- captures the first matching validation error in a pushed scope
   - Expected: status.push_error_scope(WEBGPU_ERROR_FILTER_VALIDATION) is true
   - Expected: status.report_error(WEBGPU_ERROR_FILTER_VALIDATION, "bad bind group") is true
   - Expected: status.report_error(WEBGPU_ERROR_FILTER_VALIDATION, "second validation error") is true
   - Expected: err.captured is true
   - Expected: err.kind equals `WEBGPU_ERROR_FILTER_VALIDATION`
   - Expected: err.message equals `bad bind group`
   - Expected: status.error_scope_depth() equals `0`
   - Expected: status.uncaptured_error_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("captures the first matching validation error in a pushed scope")
step("captures the first matching validation error in a pushed scope")
# @req: REQ-FEAT-WEBGPU-WEBGPU-STATUS-ERRORS-SP-001
var status = webgpu_create_status_errors()
expect(status.push_error_scope(WEBGPU_ERROR_FILTER_VALIDATION)).to_equal(true)
expect(status.report_error(WEBGPU_ERROR_FILTER_VALIDATION, "bad bind group")).to_equal(true)
expect(status.report_error(WEBGPU_ERROR_FILTER_VALIDATION, "second validation error")).to_equal(true)
val err = status.pop_error_scope()
expect(err.captured).to_equal(true)
expect(err.kind).to_equal(WEBGPU_ERROR_FILTER_VALIDATION)
expect(err.message).to_equal("bad bind group")
expect(status.error_scope_depth()).to_equal(0)
expect(status.uncaptured_error_count()).to_equal(0)
```

</details>

#### routes an error to the nearest matching nested scope

- routes an error to the nearest matching nested scope
- routes an error to the nearest matching nested scope
   - Expected: status.push_error_scope(WEBGPU_ERROR_FILTER_VALIDATION) is true
   - Expected: status.push_error_scope(WEBGPU_ERROR_FILTER_OUT_OF_MEMORY) is true
   - Expected: status.report_error(WEBGPU_ERROR_FILTER_VALIDATION, "invalid texture") is true
   - Expected: oom.captured is false
   - Expected: validation.captured is true
   - Expected: validation.message equals `invalid texture`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("routes an error to the nearest matching nested scope")
step("routes an error to the nearest matching nested scope")
var status = webgpu_create_status_errors()
expect(status.push_error_scope(WEBGPU_ERROR_FILTER_VALIDATION)).to_equal(true)
expect(status.push_error_scope(WEBGPU_ERROR_FILTER_OUT_OF_MEMORY)).to_equal(true)
expect(status.report_error(WEBGPU_ERROR_FILTER_VALIDATION, "invalid texture")).to_equal(true)
val oom = status.pop_error_scope()
val validation = status.pop_error_scope()
expect(oom.captured).to_equal(false)
expect(validation.captured).to_equal(true)
expect(validation.message).to_equal("invalid texture")
```

</details>

#### records unmatched errors as uncaptured

- records unmatched errors as uncaptured
- records unmatched errors as uncaptured
   - Expected: status.push_error_scope(WEBGPU_ERROR_FILTER_VALIDATION) is true
   - Expected: status.report_error(WEBGPU_ERROR_FILTER_INTERNAL, "device backend fault") is true
   - Expected: err.captured is false
   - Expected: status.uncaptured_error_count() equals `1`
   - Expected: status.uncaptured_errors[0].message equals `device backend fault`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("records unmatched errors as uncaptured")
step("records unmatched errors as uncaptured")
var status = webgpu_create_status_errors()
expect(status.push_error_scope(WEBGPU_ERROR_FILTER_VALIDATION)).to_equal(true)
expect(status.report_error(WEBGPU_ERROR_FILTER_INTERNAL, "device backend fault")).to_equal(true)
val err = status.pop_error_scope()
expect(err.captured).to_equal(false)
expect(status.uncaptured_error_count()).to_equal(1)
expect(status.uncaptured_errors[0].message).to_equal("device backend fault")
```

</details>

#### records errors with no scopes as uncaptured

- records errors with no scopes as uncaptured
- records errors with no scopes as uncaptured
   - Expected: status.report_error(WEBGPU_ERROR_FILTER_VALIDATION, "invalid descriptor") is true
   - Expected: status.uncaptured_error_count() equals `1`
   - Expected: status.uncaptured_errors[0].kind equals `WEBGPU_ERROR_FILTER_VALIDATION`
   - Expected: status.uncaptured_errors[0].message equals `invalid descriptor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("records errors with no scopes as uncaptured")
step("records errors with no scopes as uncaptured")
var status = webgpu_create_status_errors()
expect(status.report_error(WEBGPU_ERROR_FILTER_VALIDATION, "invalid descriptor")).to_equal(true)
expect(status.uncaptured_error_count()).to_equal(1)
expect(status.uncaptured_errors[0].kind).to_equal(WEBGPU_ERROR_FILTER_VALIDATION)
expect(status.uncaptured_errors[0].message).to_equal("invalid descriptor")
```

</details>

#### rejects unsupported filters and empty pops

- rejects unsupported filters and empty pops
- rejects unsupported filters and empty pops
   - Expected: webgpu_is_supported_error_filter("syntax") is false
   - Expected: status.push_error_scope("syntax") is false
   - Expected: status.last_error equals `GPUDevice error scope filter is not supported`
   - Expected: err.captured is false
   - Expected: status.last_error equals `GPUDevice popErrorScope requires a pushed scope`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects unsupported filters and empty pops")
step("rejects unsupported filters and empty pops")
var status = webgpu_create_status_errors()
expect(webgpu_is_supported_error_filter("syntax")).to_equal(false)
expect(status.push_error_scope("syntax")).to_equal(false)
expect(status.last_error).to_equal("GPUDevice error scope filter is not supported")
val err = status.pop_error_scope()
expect(err.captured).to_equal(false)
expect(status.last_error).to_equal("GPUDevice popErrorScope requires a pushed scope")
```

</details>

### device lost

#### starts active and records destroyed device loss

- starts active and records destroyed device loss
- starts active and records destroyed device loss
   - Expected: status.is_device_lost() is false
   - Expected: lost.lost is true
   - Expected: lost.reason equals `WEBGPU_DEVICE_LOST_REASON_DESTROYED`
   - Expected: status.is_device_lost() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("starts active and records destroyed device loss")
step("starts active and records destroyed device loss")
var status = webgpu_create_status_errors()
expect(status.is_device_lost()).to_equal(false)
val lost = status.destroy_device()
expect(lost.lost).to_equal(true)
expect(lost.reason).to_equal(WEBGPU_DEVICE_LOST_REASON_DESTROYED)
expect(status.is_device_lost()).to_equal(true)
```

</details>

#### normalizes unknown loss reasons and keeps the first loss status

- normalizes unknown loss reasons and keeps the first loss status
- normalizes unknown loss reasons and keeps the first loss status
   - Expected: webgpu_normalize_device_lost_reason("adapter-reset") equals `WEBGPU_DEVICE_LOST_REASON_UNKNOWN`
   - Expected: first.reason equals `WEBGPU_DEVICE_LOST_REASON_UNKNOWN`
   - Expected: first.message equals `adapter reset`
   - Expected: second.reason equals `WEBGPU_DEVICE_LOST_REASON_UNKNOWN`
   - Expected: second.message equals `adapter reset`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("normalizes unknown loss reasons and keeps the first loss status")
step("normalizes unknown loss reasons and keeps the first loss status")
var status = webgpu_create_status_errors()
expect(webgpu_normalize_device_lost_reason("adapter-reset")).to_equal(WEBGPU_DEVICE_LOST_REASON_UNKNOWN)
val first = status.lose_device("adapter-reset", "adapter reset")
val second = status.lose_device(WEBGPU_DEVICE_LOST_REASON_DESTROYED, "destroyed later")
expect(first.reason).to_equal(WEBGPU_DEVICE_LOST_REASON_UNKNOWN)
expect(first.message).to_equal("adapter reset")
expect(second.reason).to_equal(WEBGPU_DEVICE_LOST_REASON_UNKNOWN)
expect(second.message).to_equal("adapter reset")
```

</details>

#### clears pending error scopes when the device is lost

- clears pending error scopes when the device is lost
- clears pending error scopes when the device is lost
   - Expected: status.push_error_scope(WEBGPU_ERROR_FILTER_VALIDATION) is true
   - Expected: status.error_scope_depth() equals `1`
   - Expected: lost.lost is true
   - Expected: status.error_scope_depth() equals `0`
   - Expected: status.last_error equals `adapter reset`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("clears pending error scopes when the device is lost")
step("clears pending error scopes when the device is lost")
var status = webgpu_create_status_errors()
expect(status.push_error_scope(WEBGPU_ERROR_FILTER_VALIDATION)).to_equal(true)
expect(status.error_scope_depth()).to_equal(1)
val lost = status.lose_device("adapter-reset", "adapter reset")
expect(lost.lost).to_equal(true)
expect(status.error_scope_depth()).to_equal(0)
expect(status.last_error).to_equal("adapter reset")
```

</details>

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

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-WEBGPU-WEBGPU-STATUS-ERRORS-SP-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c861543ba75dab6fd38020c6d7df30408b0db8dd3d5f94cbb54e0d78b9b808ff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c861543ba75dab6fd38020c6d7df30408b0db8dd3d5f94cbb54e0d78b9b808ff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c861543ba75dab6fd38020c6d7df30408b0db8dd3d5f94cbb54e0d78b9b808ff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/web_platform/webgpu/webgpu_status_errors_spec.spl
mirror: doc/06_spec/feature/web_platform/webgpu/webgpu_status_errors_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/web_platform/webgpu/webgpu_status_errors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/web_platform/webgpu/webgpu_status_errors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/web_platform/webgpu/webgpu_status_errors_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/web_platform/webgpu/webgpu_status_errors_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'captures the first matching validation error in a pushed scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/webgpu/webgpu_status_errors_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes an error to the nearest matching nested scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/webgpu/webgpu_status_errors_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records unmatched errors as uncaptured' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
