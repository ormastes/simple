# Webgpu Status Errors Specification

> 1. var status = webgpu create status errors

<!-- sdn-diagram:id=webgpu_status_errors_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=webgpu_status_errors_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

webgpu_status_errors_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=webgpu_status_errors_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Webgpu Status Errors Specification

## Scenarios

### Browser WebGPU status and errors

### error scopes

#### captures the first matching validation error in a pushed scope

1. var status = webgpu create status errors
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

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var status = webgpu create status errors
   - Expected: status.push_error_scope(WEBGPU_ERROR_FILTER_VALIDATION) is true
   - Expected: status.push_error_scope(WEBGPU_ERROR_FILTER_OUT_OF_MEMORY) is true
   - Expected: status.report_error(WEBGPU_ERROR_FILTER_VALIDATION, "invalid texture") is true
   - Expected: oom.captured is false
   - Expected: validation.captured is true
   - Expected: validation.message equals `invalid texture`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var status = webgpu create status errors
   - Expected: status.push_error_scope(WEBGPU_ERROR_FILTER_VALIDATION) is true
   - Expected: status.report_error(WEBGPU_ERROR_FILTER_INTERNAL, "device backend fault") is true
   - Expected: err.captured is false
   - Expected: status.uncaptured_error_count() equals `1`
   - Expected: status.uncaptured_errors[0].message equals `device backend fault`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var status = webgpu create status errors
   - Expected: status.report_error(WEBGPU_ERROR_FILTER_VALIDATION, "invalid descriptor") is true
   - Expected: status.uncaptured_error_count() equals `1`
   - Expected: status.uncaptured_errors[0].kind equals `WEBGPU_ERROR_FILTER_VALIDATION`
   - Expected: status.uncaptured_errors[0].message equals `invalid descriptor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var status = webgpu_create_status_errors()
expect(status.report_error(WEBGPU_ERROR_FILTER_VALIDATION, "invalid descriptor")).to_equal(true)
expect(status.uncaptured_error_count()).to_equal(1)
expect(status.uncaptured_errors[0].kind).to_equal(WEBGPU_ERROR_FILTER_VALIDATION)
expect(status.uncaptured_errors[0].message).to_equal("invalid descriptor")
```

</details>

#### rejects unsupported filters and empty pops

1. var status = webgpu create status errors
   - Expected: webgpu_is_supported_error_filter("syntax") is false
   - Expected: status.push_error_scope("syntax") is false
   - Expected: status.last_error equals `GPUDevice error scope filter is not supported`
   - Expected: err.captured is false
   - Expected: status.last_error equals `GPUDevice popErrorScope requires a pushed scope`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var status = webgpu create status errors
   - Expected: status.is_device_lost() is false
   - Expected: lost.lost is true
   - Expected: lost.reason equals `WEBGPU_DEVICE_LOST_REASON_DESTROYED`
   - Expected: status.is_device_lost() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var status = webgpu_create_status_errors()
expect(status.is_device_lost()).to_equal(false)
val lost = status.destroy_device()
expect(lost.lost).to_equal(true)
expect(lost.reason).to_equal(WEBGPU_DEVICE_LOST_REASON_DESTROYED)
expect(status.is_device_lost()).to_equal(true)
```

</details>

#### normalizes unknown loss reasons and keeps the first loss status

1. var status = webgpu create status errors
   - Expected: webgpu_normalize_device_lost_reason("adapter-reset") equals `WEBGPU_DEVICE_LOST_REASON_UNKNOWN`
   - Expected: first.reason equals `WEBGPU_DEVICE_LOST_REASON_UNKNOWN`
   - Expected: first.message equals `adapter reset`
   - Expected: second.reason equals `WEBGPU_DEVICE_LOST_REASON_UNKNOWN`
   - Expected: second.message equals `adapter reset`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var status = webgpu create status errors
   - Expected: status.push_error_scope(WEBGPU_ERROR_FILTER_VALIDATION) is true
   - Expected: status.error_scope_depth() equals `1`
   - Expected: lost.lost is true
   - Expected: status.error_scope_depth() equals `0`
   - Expected: status.last_error equals `adapter reset`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var status = webgpu_create_status_errors()
expect(status.push_error_scope(WEBGPU_ERROR_FILTER_VALIDATION)).to_equal(true)
expect(status.error_scope_depth()).to_equal(1)
val lost = status.lose_device("adapter-reset", "adapter reset")
expect(lost.lost).to_equal(true)
expect(status.error_scope_depth()).to_equal(0)
expect(status.last_error).to_equal("adapter reset")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/webgpu/webgpu_status_errors_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser WebGPU status and errors
- error scopes
- device lost

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
