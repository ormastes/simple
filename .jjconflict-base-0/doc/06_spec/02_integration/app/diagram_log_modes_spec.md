# Diagram Log Modes Specification

> <details>

<!-- sdn-diagram:id=diagram_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=diagram_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

diagram_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=diagram_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Diagram Log Modes Specification

## Scenarios

### diagram log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_diagram(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json for usage output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_diagram(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"diagram\"")
expect(out).to_contain("\"status\":\"usage\"")
```

</details>

#### supports dot progress for usage output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_diagram(["--progress=dot"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("Usage: simple diagram")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_diagram(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### emits json for generated diagrams

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_diagram([
    "--log-mode=json",
    "--from-file",
    "/tmp/simple-diagram-log-modes/profile.log",
    "--output",
    "/tmp/simple-diagram-log-modes",
    "--name",
    "sample"
])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"diagram\"")
expect(out).to_contain("\"status\":\"ok\"")
expect(out).to_contain("\"generated\":1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/diagram_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- diagram log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
