# Ui Test Facade Specification

> <details>

<!-- sdn-diagram:id=ui_test_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_test_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_test_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_test_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Test Facade Specification

## Scenarios

### gc_async_mut ui_test facades

#### re-exports UI test types and JSON parsing helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elem = ElementInfo.create("btn", "button", true, false, true, false, "OK", [("role", "primary")])
expect(elem.get_id()).to_equal("btn")
expect(elem.get_kind()).to_equal("button")
expect(elem.is_visible()).to_equal(true)
match elem.get_prop("role"):
    Some(value): expect(value).to_equal("primary")
    nil: expect("").to_equal("primary")

val simple = ElementInfo.simple("label", "text")
expect(simple.is_enabled()).to_equal(true)
expect(simple.get_text()).to_equal("")

val state = UIStateInfo.default_state()
expect(state.get_mode()).to_equal("NORMAL")
expect(state.get_theme()).to_equal("default")

val json = "{\"id\":\"btn\",\"kind\":\"button\",\"visible\":true,\"focused\":false,\"enabled\":true,\"selected\":false,\"text_content\":\"OK\"}"
expect(extract_field(json, "id")).to_equal("btn")
expect(extract_bool_field(json, "visible")).to_equal(true)
val parsed = parse_element_info(json)?
expect(parsed.get_id()).to_equal("btn")
expect(parsed.get_text()).to_equal("OK")

val parsed_state = parse_state_info("{\"mode\":\"COMMAND\",\"focused_id\":\"cmd\",\"title\":\"App\",\"theme\":\"dark\",\"element_count\":3,\"protocol_version\":1}")?
expect(parsed_state.get_mode()).to_equal("COMMAND")
expect(parsed_state.get_title()).to_equal("App")

val props = parse_props("{\"label\":\"OK\",\"color\":\"blue\"}")
expect(props.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/ui_test/ui_test_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut ui_test facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
