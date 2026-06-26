# Portal Log Modes Specification

> <details>

<!-- sdn-diagram:id=portal_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=portal_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

portal_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=portal_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Portal Log Modes Specification

## Scenarios

### portal log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_portal(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("Simple Language Portal")
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json ready output

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_portal(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"portal\"")
expect(out).to_contain("\"status\":\"ready\"")
expect(out).to_contain("\"port\":3000")
```

</details>

#### supports explicit host port and migration planning

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_portal([
    "--log-mode=json",
    "--host",
    "0.0.0.0",
    "--port",
    "8080",
    "--migrate"
])
expect(code).to_equal(0)
expect(out).to_contain("\"host\":\"0.0.0.0\"")
expect(out).to_contain("\"port\":8080")
expect(out).to_contain("\"migrate\":true")
```

</details>

#### supports dot progress for help output

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_portal(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_contain(".\nSimple Language Portal")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_portal(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### renders json version output

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_portal(["--log-mode=json", "--version"])
expect(code).to_equal(0)
expect(out).to_contain("\"version\":\"0.1.0\"")
```

</details>

#### renders json unknown option output

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_portal(["--log-mode=json", "--surprise"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("Unknown portal option: --surprise")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/portal_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- portal log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
