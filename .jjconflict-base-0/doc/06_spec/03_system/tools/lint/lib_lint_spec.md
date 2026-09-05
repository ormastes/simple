# Lib Lint Specification

> <details>

<!-- sdn-diagram:id=lib_lint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lib_lint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lib_lint_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lib_lint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lib Lint Specification

## Scenarios

### Lint System: lib

<details>
<summary>Advanced: lint all lib files: no crashes</summary>

#### lint all lib files: no crashes _(slow)_

1. report crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val crashes = batch_lint(files)
    report_crashes("lint lib", crashes)
    expect(crashes.len()).to_equal(0)
else:
    print "SKIP: Simple runtime not available"
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/lint/lib_lint_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lint System: lib

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
