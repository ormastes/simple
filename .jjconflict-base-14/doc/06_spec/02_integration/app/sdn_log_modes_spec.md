# Sdn Log Modes Specification

> <details>

<!-- sdn-diagram:id=sdn_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sdn_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sdn_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sdn_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sdn Log Modes Specification

## Scenarios

### sdn log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_sdn(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("SDN CLI")
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
val (out, err, code) = _run_sdn(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"sdn\"")
expect(out).to_contain("\"status\":\"ready\"")
```

</details>

#### supports json operation planning

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_sdn(["--log-mode=json", "get", "config.sdn", "project.name"])
expect(code).to_equal(0)
expect(out).to_contain("\"status\":\"planned\"")
expect(out).to_contain("\"operation\":\"get\"")
expect(out).to_contain("\"args\":2")
```

</details>

#### renders json missing argument output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_sdn(["--log-mode=json", "set", "config.sdn"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("Command set requires 3 argument")
```

</details>

#### supports dot progress for help output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_sdn(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_contain(".\nSDN CLI")
expect(out).to_contain("Simple Data Notation")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_sdn(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### renders json unknown command output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_sdn(["--log-mode=json", "inspect"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("Unknown SDN command: inspect")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/sdn_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- sdn log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
