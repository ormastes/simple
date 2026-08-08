# Plugin Log Modes Specification

> <details>

<!-- sdn-diagram:id=plugin_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=plugin_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

plugin_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=plugin_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Plugin Log Modes Specification

## Scenarios

### plugin log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_plugin(["plugin", "--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json for empty plugin list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_plugin(["plugin", "--log-mode=json", "list"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"plugin list\"")
expect(out).to_contain("\"status\":\"ok\"")
expect(out).to_contain("\"count\":0")
```

</details>

#### supports dot progress for empty plugin list

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_plugin(["plugin", "--progress=dot", "list"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("no plugins registered")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_plugin(["plugin", "--log-mode=noisy", "list"])
expect(code).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/plugin_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- plugin log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
