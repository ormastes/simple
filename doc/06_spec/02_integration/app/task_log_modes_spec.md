# Task Log Modes Specification

> <details>

<!-- sdn-diagram:id=task_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=task_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

task_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=task_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Task Log Modes Specification

## Scenarios

### task log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_task(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("Simple Task")
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
val (out, err, code) = _run_task(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"task\"")
expect(out).to_contain("\"status\":\"ready\"")
expect(out).to_contain("\"codex\"")
```

</details>

#### supports json driver listing

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_task(["--log-mode=json", "--list"])
expect(code).to_equal(0)
expect(out).to_contain("\"drivers\"")
expect(out).to_contain("\"claude\"")
```

</details>

#### supports json planned dispatch output

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_task(["--log-mode=json", "codex", "write tests"])
expect(code).to_equal(0)
expect(out).to_contain("\"status\":\"planned\"")
expect(out).to_contain("\"driver\":\"codex\"")
expect(out).to_contain("\"description\":\"write tests\"")
```

</details>

#### supports dot progress for help output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_task(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_contain(".\nSimple Task")
expect(out).to_contain("Simple Task")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_task(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### renders json missing description output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_task(["--log-mode=json", "codex"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("Task description required for codex")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/task_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- task log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
