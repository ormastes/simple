# Browser Session Simple Script Args Specification

> <details>

<!-- sdn-diagram:id=browser_session_simple_script_args_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_simple_script_args_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_simple_script_args_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_simple_script_args_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Simple Script Args Specification

## Scenarios

### browser session simple script args

#### rejects count larger than args

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_simple_script_args_are_ints(["1"], 2)).to_equal(false)
```

</details>

#### accepts valid numeric args

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_simple_script_args_are_ints(["1", "-2"], 2)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/web/browser_session_simple_script_args_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- browser session simple script args

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
