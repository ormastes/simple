# Web Api Json Specification

> <details>

<!-- sdn-diagram:id=web_api_json_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_api_json_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_api_json_spec -> app
web_api_json_spec -> nogc_sync_mut
web_api_json_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_api_json_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Api Json Specification

## Scenarios

### state_to_json

<details>
<summary>Advanced: serializes demo state to JSON with expected fields</summary>

#### serializes demo state to JSON with expected fields _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = web_api_state_json("examples/06_io/ui/demo.ui.sdn")
expect(json.len()).to_be_greater_than(0)
expect(json).to_contain("mode")
expect(json).to_contain("NORMAL")
expect(json).to_contain("title")
expect(json).to_contain("Simple UI Demo")
expect(json).to_contain("theme")
expect(json).to_contain("dark")
expect(json).to_contain("focused_id")
```

</details>


</details>

<details>
<summary>Advanced: serializes minimal state to JSON</summary>

#### serializes minimal state to JSON _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = web_api_state_json("examples/06_io/ui/minimal.ui.sdn")
expect(json).to_contain("Minimal")
expect(json).to_contain("NORMAL")
```

</details>


</details>

### widgets_to_json

<details>
<summary>Advanced: serializes demo widgets to non-empty JSON array</summary>

#### serializes demo widgets to non-empty JSON array _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = web_api_widgets_json("examples/06_io/ui/demo.ui.sdn")
expect(json.len()).to_be_greater_than(2)
expect(json).to_start_with("[")
expect(json).to_end_with("]")
expect(json).to_contain("sidebar")
expect(json).to_contain("content")
expect(json).to_contain("status")
```

</details>


</details>

<details>
<summary>Advanced: serializes minimal widgets to non-empty JSON array</summary>

#### serializes minimal widgets to non-empty JSON array _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = web_api_widgets_json("examples/06_io/ui/minimal.ui.sdn")
expect(json.len()).to_be_greater_than(2)
expect(json).to_start_with("[")
expect(json).to_end_with("]")
expect(json).to_contain("main")
expect(json).to_contain("greeting")
expect(json).to_contain("status")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/web_api_json_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- state_to_json
- widgets_to_json

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
