# Terminal Log Modes Specification

> <details>

<!-- sdn-diagram:id=terminal_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=terminal_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

terminal_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=terminal_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Terminal Log Modes Specification

## Scenarios

### terminal log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_terminal(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("Simple Terminal")
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
val (out, err, code) = _run_terminal(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"terminal\"")
expect(out).to_contain("\"status\":\"ready\"")
```

</details>

#### supports json connect planning

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_terminal([
    "--log-mode=json",
    "connect",
    "board-a",
    "--config",
    "tmp.sdn"
])
expect(code).to_equal(0)
expect(out).to_contain("\"status\":\"planned\"")
expect(out).to_contain("\"operation\":\"connect\"")
expect(out).to_contain("\"target\":\"board-a\"")
expect(out).to_contain("\"config\":\"tmp.sdn\"")
```

</details>

#### supports json exec planning

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_terminal([
    "--log-mode=json",
    "exec",
    "board-a",
    "pwd"
])
expect(code).to_equal(0)
expect(out).to_contain("\"operation\":\"exec\"")
expect(out).to_contain("\"target\":\"board-a\"")
expect(out).to_contain("\"exec\":\"pwd\"")
```

</details>

#### supports json list planning

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_terminal(["--log-mode=json", "list"])
expect(code).to_equal(0)
expect(out).to_contain("\"status\":\"planned\"")
expect(out).to_contain("\"operation\":\"list\"")
```

</details>

#### supports dot progress for help output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_terminal(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_contain(".\nSimple Terminal")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_terminal(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### renders json missing target output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_terminal(["--log-mode=json", "disconnect"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("requires a target")
```

</details>

#### renders json missing exec command output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_terminal(["--log-mode=json", "exec", "board-a"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("requires a command")
```

</details>

#### renders json unknown option output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_terminal(["--log-mode=json", "--surprise"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("Unknown terminal option: --surprise")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/terminal_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- terminal log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
