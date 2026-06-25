# Ui Browser Log Modes Specification

> <details>

<!-- sdn-diagram:id=ui_browser_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_browser_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_browser_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_browser_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Browser Log Modes Specification

## Scenarios

### ui.browser log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_ui_browser(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("Simple UI Browser")
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
val (out, err, code) = _run_ui_browser(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"ui.browser\"")
expect(out).to_contain("\"status\":\"ready\"")
```

</details>

#### supports json browser planning

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_ui_browser([
    "--log-mode=json",
    "examples/06_io/ui/demo.ui.sdn",
    "--snapshot",
    "tmp.ppm",
    "--backend",
    "software",
    "--ui-access-db",
    "access.db",
    "--open",
    "--shared-wm"
])
expect(code).to_equal(0)
expect(out).to_contain("\"status\":\"planned\"")
expect(out).to_contain("\"file\":\"examples/06_io/ui/demo.ui.sdn\"")
expect(out).to_contain("\"snapshot\":\"tmp.ppm\"")
expect(out).to_contain("\"backend\":\"software\"")
expect(out).to_contain("\"ui_access_db\":\"access.db\"")
expect(out).to_contain("\"open\":true")
expect(out).to_contain("\"shared_wm\":true")
```

</details>

#### supports dot progress for help output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_ui_browser(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_contain(".\nSimple UI Browser")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_ui_browser(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### renders json missing file output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_ui_browser(["--log-mode=json", "--open"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("requires a UI SDN file")
```

</details>

#### renders json unknown option output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_ui_browser(["--log-mode=json", "--surprise"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("Unknown ui.browser option: --surprise")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/ui_browser_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ui.browser log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
