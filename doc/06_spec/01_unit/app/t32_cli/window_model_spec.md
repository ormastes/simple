# Window Model Specification

> <details>

<!-- sdn-diagram:id=window_model_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=window_model_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

window_model_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=window_model_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Model Specification

## Scenarios

### T32 Window Model

#### lists windows by key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var keys: [text] = ["break_list", "register_view", "var_local"]
expect(keys.len()).to_equal(3)
expect(keys[0]).to_equal("break_list")
```

</details>

#### finds window by key

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var keys: [text] = ["break_list", "register_view", "var_local"]
var found = ""
for k in keys:
    if k == "register_view":
        found = k
expect(found).to_equal("register_view")
```

</details>

#### describes window actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var actions: [text] = ["set_break", "clear_break", "go"]
expect(actions.len()).to_equal(3)
expect(actions[0]).to_equal("set_break")
```

</details>

#### describes window fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fields: [text] = ["symbol", "address"]
expect(fields.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/t32_cli/window_model_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 Window Model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
