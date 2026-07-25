# Init Log Modes Specification

> 1.  setup fixture

<!-- sdn-diagram:id=init_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=init_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

init_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=init_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Init Log Modes Specification

## Scenarios

### init log mode CLI options

#### shows shared log options in help

1.  setup fixture
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_init(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports minimal log-mode json

1.  setup fixture
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_init(["sample-init", "--minimal", "--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"init\"")
expect(out).to_contain("\"name\":\"sample-init\"")
expect(out).to_contain("\"minimal\":true")
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
val (out, err, code) = _run_init(["sample-init", "--minimal", "--progress=dot"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("Initialized Simple project 'sample-init' (minimal)")
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
val (out, err, code) = _run_init(["sample-init", "--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/init_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- init log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
