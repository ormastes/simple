# Test Script Trace2 Specification

> <details>

<!-- sdn-diagram:id=test_script_trace2_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_script_trace2_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_script_trace2_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_script_trace2_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Script Trace2 Specification

## Scenarios

### trace2

#### print literal produces output

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><script>print(\"hello\")</script></body></html>"
val result = execute_scripts_in_html(html)
expect(result.scripts_executed).to_equal(1)
expect(result.console_output.len()).to_equal(1)
expect(result.console_output[0]).to_equal("hello")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/test_script_trace2_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- trace2

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
