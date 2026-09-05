# List Constructor Hardening Specification

> <details>

<!-- sdn-diagram:id=list_constructor_hardening_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=list_constructor_hardening_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

list_constructor_hardening_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=list_constructor_hardening_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# List Constructor Hardening Specification

## Scenarios

### List constructor hardening

#### keeps owned src code off the crashing direct generic List constructor

- ["-n", "List<[^>]+>\\
   - Expected: code equals `1`
   - Expected: stdout.trim() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _stderr, code) = rt_process_run(
    "rg",
    ["-n", "List<[^>]+>\\(\\)", "src", "-g", "*.spl"]
)

expect(code).to_equal(1)
expect(stdout.trim()).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/core/list_constructor_hardening_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- List constructor hardening

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
