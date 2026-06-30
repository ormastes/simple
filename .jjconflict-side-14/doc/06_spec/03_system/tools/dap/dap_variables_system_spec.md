# Dap Variables System Specification

> <details>

<!-- sdn-diagram:id=dap_variables_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dap_variables_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dap_variables_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dap_variables_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dap Variables System Specification

## Scenarios

### DAP System: variable inspection

<details>
<summary>Advanced: type system and semantics files parse without crashes</summary>

#### type system and semantics files parse without crashes _(slow)_

1. report crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val crashes = check_lint_parse_dirs(["src/compiler/30.types", "src/compiler/35.semantics"])
    report_crashes("variables lint", crashes)
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
| Source | `test/03_system/tools/dap/dap_variables_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DAP System: variable inspection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
