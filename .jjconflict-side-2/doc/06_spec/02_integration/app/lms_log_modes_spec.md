# Lms Log Modes Specification

> <details>

<!-- sdn-diagram:id=lms_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lms_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lms_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lms_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lms Log Modes Specification

## Scenarios

### lms log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_lms(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("Simple Language Model Server")
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json ready output

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_lms(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"lms\"")
expect(out).to_contain("\"status\":\"ready\"")
expect(out).to_contain("\"port\":8765")
```

</details>

#### supports dot progress for help output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_lms(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("Simple Language Model Server")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_lms(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### renders json version output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_lms(["--log-mode=json", "--version"])
expect(code).to_equal(0)
expect(out).to_contain("\"version\":\"0.1.0\"")
```

</details>

#### includes explicit port in json readiness output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_lms(["--log-mode=json", "--port", "9999"])
expect(code).to_equal(0)
expect(out).to_contain("\"port\":9999")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/lms_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- lms log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
