# Remote Test Log Modes Specification

> <details>

<!-- sdn-diagram:id=remote_test_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=remote_test_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

remote_test_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=remote_test_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Remote Test Log Modes Specification

## Scenarios

### remote-test log mode CLI options

#### shows shared log options in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_remote_test(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("Simple Remote Test")
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
val (out, err, code) = _run_remote_test(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"remote-test\"")
expect(out).to_contain("\"status\":\"ready\"")
```

</details>

#### supports json command planning

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_remote_test([
    "--log-mode=json",
    "test-host",
    "test/unit/lib/math_spec.spl",
    "--config",
    "tmp.sdn",
    "--simple-bin",
    "build/simple"
])
expect(code).to_equal(0)
expect(out).to_contain("\"status\":\"planned\"")
expect(out).to_contain("\"terminal\":\"test-host\"")
expect(out).to_contain("\"test_path\":\"test/unit/lib/math_spec.spl\"")
expect(out).to_contain("\"config\":\"tmp.sdn\"")
expect(out).to_contain("\"remote_simple_bin\":\"build/simple\"")
```

</details>

#### supports dot progress for help output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_remote_test(["--progress=dot", "--help"])
expect(code).to_equal(0)
expect(out).to_contain(".\nSimple Remote Test")
```

</details>

#### rejects invalid log mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_remote_test(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

#### renders json missing argument output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_remote_test(["--log-mode=json", "test-host"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("requires a terminal name and test path")
```

</details>

#### renders json unknown option output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = _run_remote_test(["--log-mode=json", "--surprise"])
expect(code).to_equal(1)
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("Unknown remote-test option: --surprise")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/remote_test_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- remote-test log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
