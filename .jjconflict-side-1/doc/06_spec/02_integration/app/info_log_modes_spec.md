# Info Log Modes Specification

> 1.  setup fixture

<!-- sdn-diagram:id=info_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=info_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

info_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=info_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Info Log Modes Specification

## Scenarios

### info log mode CLI options

#### shows shared log options in help

1.  setup fixture
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_info(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports project log-mode json

1.  setup fixture
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_info(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"info\"")
expect(out).to_contain("\"kind\":\"project\"")
expect(out).to_contain("\"name\":\"sample-info\"")
```

</details>

#### supports package log-mode json

1.  setup fixture
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_info(["sample-pkg", "--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"kind\":\"package\"")
expect(out).to_contain("\"name\":\"sample-pkg\"")
```

</details>

#### supports dot progress

1.  setup fixture
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_info(["--progress=dot"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("Project Info")
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
val (out, err, code) = _run_info(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/info_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- info log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
