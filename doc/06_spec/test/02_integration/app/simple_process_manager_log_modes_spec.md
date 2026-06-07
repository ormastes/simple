# Simple Process Manager Log Modes Specification

> <details>

<!-- sdn-diagram:id=simple_process_manager_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_process_manager_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_process_manager_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_process_manager_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Process Manager Log Modes Specification

## Scenarios

### simple process manager log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_spm(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json for ready output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_spm(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"simple-process-manager\"")
expect(out).to_contain("\"status\":\"ready\"")
```

</details>

#### supports dot progress for help output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_spm(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("Simple Process Manager")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_spm(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### emits json for unknown commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_spm(["--log-mode=json", "bogus"])
expect(code).to_equal(1)
expect(out).to_contain("\"command\":\"simple-process-manager\"")
expect(out).to_contain("\"status\":\"error\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/simple_process_manager_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- simple process manager log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
