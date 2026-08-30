# Test Analysis Log Modes Specification

> <details>

<!-- sdn-diagram:id=test_analysis_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_analysis_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_analysis_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_analysis_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Analysis Log Modes Specification

## Scenarios

### test analysis log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_test_analysis(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("Test Failure Analysis")
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json ready output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_test_analysis(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"test-analysis\"")
expect(out).to_contain("\"status\":\"ready\"")
```

</details>

#### supports json classification output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_test_analysis(["--log-mode=json", "classify", "parse error"])
expect(code).to_equal(0)
expect(out).to_contain("\"operation\":\"classify\"")
expect(out).to_contain("\"errorType\":\"parse_error\"")
```

</details>

#### supports json feature extraction output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_test_analysis(["--log-mode=json", "extract", "expected expression, found At"])
expect(code).to_equal(0)
expect(out).to_contain("\"operation\":\"extract\"")
expect(out).to_contain("\"feature\":\"matrix_multiplication\"")
```

</details>

#### supports json analyze planning

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_test_analysis(["--log-mode=json", "analyze", "--db=tmp.sdn"])
expect(code).to_equal(0)
expect(out).to_contain("\"status\":\"planned\"")
expect(out).to_contain("\"operation\":\"analyze\"")
```

</details>

#### supports dot progress for help output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_test_analysis(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_contain(".\nTest Failure Analysis")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_test_analysis(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### renders json missing message output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_test_analysis(["--log-mode=json", "classify"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("Command classify requires an error message")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/test_analysis_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- test analysis log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
