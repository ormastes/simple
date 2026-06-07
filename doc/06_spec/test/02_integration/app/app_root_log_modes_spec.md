# App Root Log Modes Specification

> <details>

<!-- sdn-diagram:id=app_root_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=app_root_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

app_root_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=app_root_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# App Root Log Modes Specification

## Scenarios

### app root log mode CLI options

#### keeps plain invocation quiet

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_app_root([])
expect(code).to_equal(0)
expect(out).to_equal("")
```

</details>

#### shows shared log options in help

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_app_root(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("Simple app root entrypoint")
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json for ready output

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_app_root(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"app-root\"")
expect(out).to_contain("\"status\":\"ready\"")
```

</details>

#### supports dot progress for help output

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_app_root(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("Simple app root entrypoint")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_app_root(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/app_root_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- app root log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
