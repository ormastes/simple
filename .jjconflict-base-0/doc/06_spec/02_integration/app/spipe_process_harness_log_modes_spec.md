# Spipe Process Harness Log Modes Specification

> 1.  setup fixture

<!-- sdn-diagram:id=spipe_process_harness_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spipe_process_harness_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

spipe_process_harness_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spipe_process_harness_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spipe Process Harness Log Modes Specification

## Scenarios

### spipe-process-harness log mode CLI options

#### shows shared log options in help

1.  setup fixture
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_harness(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json for state

1.  setup fixture
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_harness(["--log-mode=json", "state", "--feature", "sample", "--approved"])
expect(code).to_equal(0)
expect(out).to_contain("\"command\":\"spipe-process-harness state\"")
expect(out).to_contain("\"status\":\"ok\"")
expect(out).to_contain(".spipe/sample/state.md")
```

</details>

#### supports dot progress for state

1.  setup fixture
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_harness(["--progress=dot", "state", "--feature", "sample", "--approved"])
expect(code).to_equal(0)
expect(out).to_contain(".")
expect(out).to_contain(".spipe/sample/state.md")
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
val (out, err, code) = _run_harness(["--log-mode=noisy", "state"])
expect(code).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/spipe_process_harness_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- spipe-process-harness log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
