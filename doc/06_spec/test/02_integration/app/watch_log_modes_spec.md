# Watch Log Modes Specification

> <details>

<!-- sdn-diagram:id=watch_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=watch_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

watch_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=watch_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Watch Log Modes Specification

## Scenarios

### watch log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_watch(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json for missing watch path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_watch(["--log-mode=json", "--path=/tmp/simple-watch-missing-path"])
expect(code).to_equal(1)
expect(out).to_contain("\"command\":\"watch\"")
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("\"path\":\"/tmp/simple-watch-missing-path\"")
```

</details>

#### supports dot progress for missing watch path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_watch(["--progress=dot", "--path=/tmp/simple-watch-missing-path"])
expect(code).to_equal(1)
expect(out).to_start_with(".")
expect(out).to_contain("Error: watch path not found")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_watch(["--log-mode=noisy", "--path=/tmp/simple-watch-missing-path"])
expect(code).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/watch_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- watch log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
