# Adaptive Scaffold Specification

> <details>

<!-- sdn-diagram:id=adaptive_scaffold_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=adaptive_scaffold_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

adaptive_scaffold_spec -> std
adaptive_scaffold_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=adaptive_scaffold_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adaptive Scaffold Specification

## Scenarios

### adaptive_nav_scaffold phone portrait

#### nav_pattern prop == bottom

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ff = phone_portrait_ff()
val root = adaptive_nav_scaffold("nav_root", make_items(), make_content(), ff)
expect(root.get_prop("nav_pattern")).to_equal("bottom")
```

</details>

#### root is a column layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ff = phone_portrait_ff()
val root = adaptive_nav_scaffold("nav_root2", make_items(), make_content(), ff)
expect(root.layout()).to_equal("vbox")
```

</details>

#### nav bar contains all 4 item ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ff = phone_portrait_ff()
val root = adaptive_nav_scaffold("nav_root3", make_items(), make_content(), ff)
# In bottom layout: column([content, nav_bar])
# nav_bar is the second child; its children are the item buttons
val nav_bar = root.child_at(1)
expect(nav_bar != nil).to_equal(true)
# Collect all descendant ids
val all_ids = root.collect_ids()
val has_home     = all_ids.contains("home")
val has_search   = all_ids.contains("search")
val has_library  = all_ids.contains("library")
val has_settings = all_ids.contains("settings")
expect(has_home).to_equal(true)
expect(has_search).to_equal(true)
expect(has_library).to_equal(true)
expect(has_settings).to_equal(true)
```

</details>

#### nav item buttons carry min_height == 44 (ios apple touch)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ff = phone_portrait_ff()
val root = adaptive_nav_scaffold("nav_root4", make_items(), make_content(), ff)
val home_btn = root.find_by_id("home")
expect(home_btn != nil).to_equal(true)
expect(home_btn.get_prop("min_height")).to_equal("44")
```

</details>

### adaptive_nav_scaffold landscape phone

#### nav_pattern == rail (NOT bottom) for height-Compact ios landscape

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ff = landscape_phone_ff()
expect(ff.layout.vertical).to_equal(SizeClass.Compact)
val root = adaptive_nav_scaffold("nav_ls_root", make_items(), make_content(), ff)
expect(root.get_prop("nav_pattern")).to_equal("rail")
```

</details>

### adaptive_nav_scaffold tablet landscape

#### 1024x768 ipados Expanded → nav_pattern == sidebar

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ff = tablet_landscape_ff()
expect(ff.layout.horizontal).to_equal(SizeClass.Expanded)
val root = adaptive_nav_scaffold("nav_tab_exp", make_items(), make_content(), ff)
expect(root.get_prop("nav_pattern")).to_equal("sidebar")
```

</details>

### adaptive_nav_scaffold tablet portrait 700x1000 android Regular

#### 700x1000 android Regular → nav_pattern == rail

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ff = tablet_portrait_ff()
expect(ff.layout.horizontal).to_equal(SizeClass.Regular)
val root = adaptive_nav_scaffold("nav_tab_reg", make_items(), make_content(), ff)
expect(root.get_prop("nav_pattern")).to_equal("rail")
```

</details>

### adaptive_nav_scaffold desktop

#### 1440x900 macos → nav_pattern == sidebar

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ff = desktop_ff()
val root = adaptive_nav_scaffold("nav_desk", make_items(), make_content(), ff)
expect(root.get_prop("nav_pattern")).to_equal("sidebar")
```

</details>

#### desktop nav items carry min_height == 32 (dense desktop)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ff = desktop_ff()
val root = adaptive_nav_scaffold("nav_desk2", make_items(), make_content(), ff)
val home_btn = root.find_by_id("home")
expect(home_btn != nil).to_equal(true)
expect(home_btn.get_prop("min_height")).to_equal("32")
```

</details>

### adaptive_nav_scaffold resize re-selection

#### 390x844 → bottom, then 1440x900 → sidebar (pure function)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ff_phone = compute_form_factor(new_viewport(390, 844, "gui"), "ios", true)
val root_phone = adaptive_nav_scaffold("nav_resize_phone", make_items(), make_content(), ff_phone)
expect(root_phone.get_prop("nav_pattern")).to_equal("bottom")

val ff_desktop = compute_form_factor(new_viewport(1440, 900, "gui"), "macos", false)
val root_desktop = adaptive_nav_scaffold("nav_resize_desktop", make_items(), make_content(), ff_desktop)
expect(root_desktop.get_prop("nav_pattern")).to_equal("sidebar")
```

</details>

### list_detail_scaffold desktop two_pane

#### 1440x900 macos Expanded → list_detail == two_pane with both children

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ff = desktop_ff()
val root = list_detail_scaffold("ld_desk", make_list_node(), make_detail_node(), ff, false)
expect(root.get_prop("list_detail")).to_equal("two_pane")
val all_ids = root.collect_ids()
expect(all_ids.contains("list_pane")).to_equal(true)
expect(all_ids.contains("detail_pane")).to_equal(true)
```

</details>

### list_detail_scaffold phone single_list

#### 390x844 ios show_detail=false → list_detail == single_list, detail absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ff = phone_portrait_ff()
val root = list_detail_scaffold("ld_phone_list", make_list_node(), make_detail_node(), ff, false)
expect(root.get_prop("list_detail")).to_equal("single_list")
val all_ids = root.collect_ids()
expect(all_ids.contains("list_pane")).to_equal(true)
expect(all_ids.contains("detail_pane")).to_equal(false)
```

</details>

### list_detail_scaffold phone single_detail

#### 390x844 ios show_detail=true → list_detail == single_detail, list absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ff = phone_portrait_ff()
val root = list_detail_scaffold("ld_phone_detail", make_list_node(), make_detail_node(), ff, true)
expect(root.get_prop("list_detail")).to_equal("single_detail")
val all_ids = root.collect_ids()
expect(all_ids.contains("detail_pane")).to_equal(true)
expect(all_ids.contains("list_pane")).to_equal(false)
```

</details>

#### single_detail has back_nav=true on detail node

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ff = phone_portrait_ff()
val root = list_detail_scaffold("ld_phone_detail2", make_list_node(), make_detail_node(), ff, true)
val detail = root.find_by_id("detail_pane")
expect(detail != nil).to_equal(true)
expect(detail.get_prop("back_nav")).to_equal("true")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/adaptive_scaffold_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- adaptive_nav_scaffold phone portrait
- adaptive_nav_scaffold landscape phone
- adaptive_nav_scaffold tablet landscape
- adaptive_nav_scaffold tablet portrait 700x1000 android Regular
- adaptive_nav_scaffold desktop
- adaptive_nav_scaffold resize re-selection
- list_detail_scaffold desktop two_pane
- list_detail_scaffold phone single_list
- list_detail_scaffold phone single_detail

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
