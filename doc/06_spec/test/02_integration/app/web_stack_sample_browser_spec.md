# Web Stack Sample Browser Specification

> <details>

<!-- sdn-diagram:id=web_stack_sample_browser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_stack_sample_browser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_stack_sample_browser_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_stack_sample_browser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Stack Sample Browser Specification

## Scenarios

### web_stack_sample browser lane contracts

#### uses plain html forms that the simple browser page adapter can drive

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = read_source(APP_SOURCE)
val browser = read_source(BROWSER_PAGE)
expect(browser).to_contain("fn simple_browser_submit_request")
expect(browser).to_contain("fn simple_browser_set_field_value")
expect(app).to_contain("<input type=\\\"text\\\" name=\\\"username\\\"")
expect(app).to_contain("<input type=\\\"text\\\" name=\\\"password\\\"")
expect(app).to_contain("<input type=\\\"text\\\" name=\\\"title\\\"")
expect(app).to_contain("<textarea name=\\\"details\\\">")
expect(app).to_contain("<input type=\\\"search\\\" name=\\\"q\\\"")
```

</details>

#### keeps route targets explicit for login create search and logout

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = read_source(APP_SOURCE)
expect(app).to_contain("action=\\\"/login\\\"")
expect(app).to_contain("action=\\\"/register\\\"")
expect(app).to_contain("action=\\\"/items/new\\\"")
expect(app).to_contain("action=\\\"/items/search\\\"")
expect(app).to_contain("action=\\\"/logout\\\"")
expect(app).to_contain("action=\\\"/items/")
expect(app).to_contain("/delete\\\"><button type=\\\"submit\\\">Delete</button>")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/web_stack_sample_browser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- web_stack_sample browser lane contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
