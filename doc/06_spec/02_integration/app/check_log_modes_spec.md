# Check Log Modes Specification

> 1.  setup fixture

<!-- sdn-diagram:id=check_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=check_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

check_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=check_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Check Log Modes Specification

## Scenarios

### check log mode CLI options

#### shows shared log options in help

1.  setup fixture
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_check(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json

1.  setup fixture
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_check(["--log-mode=json", "missing.spl"])
expect(code).to_equal(1)
expect(out).to_contain("\"command\":\"check\"")
expect(out).to_contain("\"status\":\"error\"")
expect(out).to_contain("\"files\":1")
```

</details>

#### supports dot progress

1.  setup fixture
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_check(["--progress=dot", "missing.spl"])
expect(code).to_equal(1)
expect(out).to_contain(".")
expect(out).to_contain("ERROR: file not found: missing.spl")
```

</details>

#### rejects invalid log mode

1.  setup fixture
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_check(["--log-mode=noisy", "sample.spl"])
expect(code).to_equal(1)
```

</details>

### JSON applies SSpec guidance without contaminating output

Checking one valid source and one SSpec command-block source with `--json`
returns exit 1 and exactly one compact JSON object. The summary reports two
checked files, one error, and one file with errors; guidance text is suppressed
from machine output.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/check_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- check log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
