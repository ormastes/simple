# Sgtti Specification

> <details>

<!-- sdn-diagram:id=sgtti_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sgtti_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sgtti_spec -> std
sgtti_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sgtti_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sgtti Specification

## Scenarios

### SGTTI UI test driver

#### finds an element by canonical id

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = SgttiTestDriver.new(_sgtti_fixture_snapshot())
val node = driver.get_element("surface:main#button_ok").unwrap()
expect(node.widget_id).to_equal("button_ok")
```

</details>

#### finds an element by widget id

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = SgttiTestDriver.new(_sgtti_fixture_snapshot())
val node = driver.get_element("name_input").unwrap()
expect(node.canonical_id).to_equal("surface:main#name_input")
```

</details>

#### returns all elements

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = SgttiTestDriver.from_snapshot(_sgtti_fixture_snapshot())
val nodes = driver.get_elements().unwrap()
expect(nodes.len()).to_equal(2)
```

</details>

#### delegates filtered node queries to WinText

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = SgttiTestDriver.new(_sgtti_fixture_snapshot())
val nodes = driver.find_nodes("surface:main", "input", "Ada", 10).unwrap()
expect(nodes.len()).to_equal(1)
expect(nodes[0].widget_id).to_equal("name_input")
```

</details>

#### checks visibility, focus, enabled, selected, existence, and text

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = SgttiTestDriver.new(_sgtti_fixture_snapshot())
expect(driver.check_exists("button_ok").unwrap()).to_equal(true)
expect(driver.check_visible("button_ok").unwrap()).to_equal(true)
expect(driver.check_focused("button_ok").unwrap()).to_equal(false)
expect(driver.check_enabled("button_ok").unwrap()).to_equal(true)
expect(driver.check_selected("button_ok").unwrap()).to_equal(false)
expect(driver.check_text("button_ok", "primary").unwrap()).to_equal(true)
```

</details>

#### routes click and type_text actions

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = SgttiTestDriver.new(_sgtti_fixture_snapshot())
expect(driver.click("button_ok").unwrap()).to_equal(true)
expect(driver.type_text("name_input", "Grace").unwrap()).to_equal(true)
```

</details>

#### reports missing and unsupported targets

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = SgttiTestDriver.new(_sgtti_fixture_snapshot())
expect(driver.check_exists("missing").unwrap()).to_equal(false)
expect(driver.get_element("missing").is_err()).to_equal(true)
expect(driver.click("name_input").is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/ui_test/sgtti_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SGTTI UI test driver

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
