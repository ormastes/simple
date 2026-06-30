# Dap Breakpoint System Specification

> <details>

<!-- sdn-diagram:id=dap_breakpoint_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dap_breakpoint_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dap_breakpoint_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dap_breakpoint_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dap Breakpoint System Specification

## Scenarios

### DAP System: breakpoint resolution

<details>
<summary>Advanced: DAP modules parse without crashes</summary>

#### DAP modules parse without crashes _(slow)_

1. report crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val crashes = check_lint_parse_dirs(["src/lib/nogc_sync_mut/dap"])
    report_crashes("DAP module parse", crashes)
    expect(crashes.len()).to_equal(0)
else:
    print "SKIP: Simple runtime not available"
```

</details>


</details>

<details>
<summary>Advanced: sample app files parse without crashes</summary>

#### sample app files parse without crashes _(slow)_

1. report crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val crashes = check_lint_parse_dirs(["src/app"])
    report_crashes("app file parse", crashes)
    expect(crashes.len()).to_equal(0)
else:
    print "SKIP: Simple runtime not available"
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Developer Tools |
| Status | Active |
| Source | `test/03_system/tools/dap/dap_breakpoint_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DAP System: breakpoint resolution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 2 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
