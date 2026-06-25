# Tooling Log Modes Specification

> <details>

<!-- sdn-diagram:id=tooling_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tooling_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tooling_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tooling_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tooling Log Modes Specification

## Scenarios

### tooling log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_tooling(["help"])
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
val (out, err, code) = _run_tooling(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"tooling\"")
expect(out).to_contain("\"status\":\"usage\"")
```

</details>

#### supports dot progress for usage output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_tooling(["--progress=dot"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("Simple Multi-Language Tooling CLI")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_tooling(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### emits json for deterministic command output

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_tooling(["--log-mode=json", "build", "--release"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"tooling\"")
expect(out).to_contain("\"status\":\"ok\"")
expect(out).to_contain("\"action\":\"build\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/tooling_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- tooling log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
