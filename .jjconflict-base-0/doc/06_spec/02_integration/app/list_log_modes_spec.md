# List Log Modes Specification

> 1.  setup fixture

<!-- sdn-diagram:id=list_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=list_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

list_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=list_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# List Log Modes Specification

## Scenarios

### list log mode CLI options

#### shows shared log options in help

1.  setup fixture
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_list(["--help"])
expect(code).to_equal(0)
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json

1.  setup fixture
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_fixture()
val (out, err, code) = _run_list(["--log-mode=json"])
expect(code).to_equal(0)
expect(out).to_contain("\"dependencies\":{\"alpha\":\"*\",\"beta\":\"*\"}")
expect(out).to_contain("\"dev_dependencies\":{\"gamma\":\"*\"}")
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
val (out, err, code) = _run_list(["--progress=dot"])
expect(code).to_equal(0)
expect(out).to_start_with(".")
expect(out).to_contain("list-fixture v1.2.3")
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
val (out, err, code) = _run_list(["--log-mode=noisy"])
expect(code).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/list_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- list log mode CLI options

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
