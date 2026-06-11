# Menu Specification

> 1. expect m item count

<!-- sdn-diagram:id=menu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=menu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

menu_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=menu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Menu Specification

## Scenarios

### Menu.new

#### has 0 items

1. expect m item count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Menu.new(1)
expect m.item_count() to_equal 0
```

</details>

#### append bumps count

1. var m = Menu new
2. m append
3. expect m item count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = Menu.new(1)
m.append(_normal_item(1, "File"))
expect m.item_count() to_equal 1
```

</details>

#### append twice gives count 2

1. var m = Menu new
2. m append
3. m append
4. expect m item count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = Menu.new(1)
m.append(_normal_item(1, "File"))
m.append(_normal_item(2, "Edit"))
expect m.item_count() to_equal 2
```

</details>

### MenuItem kinds

#### Separator kind round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sep = MenuItem(
    id: 0,
    label: "",
    kind: MenuItemKind.Separator,
    enabled: false,
    checked: false,
    accelerator: "",
    submenu_id: -1
)
val is_sep = sep.submenu_id == -1
expect is_sep to_equal true
```

</details>

#### accelerator text round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = MenuItem(
    id: 5,
    label: "Save",
    kind: MenuItemKind.Normal,
    enabled: true,
    checked: false,
    accelerator: "Ctrl+S",
    submenu_id: -1
)
expect item.accelerator to_equal "Ctrl+S"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gui/menu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Menu.new
- MenuItem kinds

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
