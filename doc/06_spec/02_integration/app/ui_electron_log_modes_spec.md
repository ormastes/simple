# Ui Electron Log Modes Specification

> <details>

<!-- sdn-diagram:id=ui_electron_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_electron_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_electron_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_electron_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Electron Log Modes Specification

## Scenarios

### ui electron log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_ui_electron(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("Simple UI Electron dev-preview entrypoint")
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
val (out, err, code) = _run_ui_electron(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"ui.electron\"")
expect(out).to_contain("\"status\":\"ready\"")
```

</details>

#### supports dot progress for help output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_ui_electron(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("Simple UI Electron dev-preview entrypoint")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_ui_electron(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### emits json for unknown commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_ui_electron(["--log-mode=json", "bogus"])
expect(code).to_equal(1)
expect(out).to_contain("\"command\":\"ui.electron\"")
expect(out).to_contain("\"status\":\"error\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/ui_electron_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ui electron log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
