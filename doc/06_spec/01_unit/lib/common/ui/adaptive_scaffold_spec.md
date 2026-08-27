# Adaptive Scaffold Specification

> Tests covering adaptive_nav_scaffold phone portrait, adaptive_nav_scaffold landscape phone, adaptive_nav_scaffold tablet landscape, adaptive_nav_scaffold tablet portrait 700x1000 android Regular, adaptive_nav_scaffold desktop, adaptive_nav_scaffold resize re-selection, list_detail_scaffold desktop two_pane, list_detail_scaffold phone single_list, list_detail_scaffold phone single_detail.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adaptive Scaffold Specification

## Scenarios

### adaptive_nav_scaffold phone portrait

#### nav_pattern prop == bottom

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- nav_pattern prop == bottom
   - Expected: root.get_prop("nav_pattern") equals `bottom`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nav_pattern prop == bottom")
val ff = phone_portrait_ff()
val root = adaptive_nav_scaffold("nav_root", make_items(), make_content(), ff)
expect(root.get_prop("nav_pattern")).to_equal("bottom")
```

</details>

#### root is a column layout

- root is a column layout
   - Expected: root.layout() equals `vbox`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("root is a column layout")
val ff = phone_portrait_ff()
val root = adaptive_nav_scaffold("nav_root2", make_items(), make_content(), ff)
expect(root.layout()).to_equal("vbox")
```

</details>

#### nav bar contains all 4 item ids

- nav bar contains all 4 item ids
   - Expected: nav_bar != nil is true
   - Expected: has_home is true
   - Expected: has_search is true
   - Expected: has_library is true
   - Expected: has_settings is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nav bar contains all 4 item ids")
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

- nav item buttons carry min_height == 44 (ios apple touch)
   - Expected: home_btn != nil is true
   - Expected: home_btn.get_prop("min_height") equals `44`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nav item buttons carry min_height == 44 (ios apple touch)")
val ff = phone_portrait_ff()
val root = adaptive_nav_scaffold("nav_root4", make_items(), make_content(), ff)
val home_btn = root.find_by_id("home")
expect(home_btn != nil).to_equal(true)
expect(home_btn.get_prop("min_height")).to_equal("44")
```

</details>

### adaptive_nav_scaffold landscape phone

#### nav_pattern == rail (NOT bottom) for height-Compact ios landscape

- nav_pattern == rail (NOT bottom) for height-Compact ios landscape
   - Expected: ff.layout.vertical equals `SizeClass.Compact`
   - Expected: root.get_prop("nav_pattern") equals `rail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nav_pattern == rail (NOT bottom) for height-Compact ios landscape")
val ff = landscape_phone_ff()
expect(ff.layout.vertical).to_equal(SizeClass.Compact)
val root = adaptive_nav_scaffold("nav_ls_root", make_items(), make_content(), ff)
expect(root.get_prop("nav_pattern")).to_equal("rail")
```

</details>

### adaptive_nav_scaffold tablet landscape

#### 1024x768 ipados Expanded → nav_pattern == sidebar

- 1024x768 ipados Expanded → nav_pattern == sidebar
   - Expected: ff.layout.horizontal equals `SizeClass.Expanded`
   - Expected: root.get_prop("nav_pattern") equals `sidebar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1024x768 ipados Expanded → nav_pattern == sidebar")
val ff = tablet_landscape_ff()
expect(ff.layout.horizontal).to_equal(SizeClass.Expanded)
val root = adaptive_nav_scaffold("nav_tab_exp", make_items(), make_content(), ff)
expect(root.get_prop("nav_pattern")).to_equal("sidebar")
```

</details>

### adaptive_nav_scaffold tablet portrait 700x1000 android Regular

#### 700x1000 android Regular → nav_pattern == rail

- 700x1000 android Regular → nav_pattern == rail
   - Expected: ff.layout.horizontal equals `SizeClass.Regular`
   - Expected: root.get_prop("nav_pattern") equals `rail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("700x1000 android Regular → nav_pattern == rail")
val ff = tablet_portrait_ff()
expect(ff.layout.horizontal).to_equal(SizeClass.Regular)
val root = adaptive_nav_scaffold("nav_tab_reg", make_items(), make_content(), ff)
expect(root.get_prop("nav_pattern")).to_equal("rail")
```

</details>

### adaptive_nav_scaffold desktop

#### 1440x900 macos → nav_pattern == sidebar

- 1440x900 macos → nav_pattern == sidebar
   - Expected: root.get_prop("nav_pattern") equals `sidebar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1440x900 macos → nav_pattern == sidebar")
val ff = desktop_ff()
val root = adaptive_nav_scaffold("nav_desk", make_items(), make_content(), ff)
expect(root.get_prop("nav_pattern")).to_equal("sidebar")
```

</details>

#### desktop nav items carry min_height == 32 (dense desktop)

- desktop nav items carry min_height == 32 (dense desktop)
   - Expected: home_btn != nil is true
   - Expected: home_btn.get_prop("min_height") equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("desktop nav items carry min_height == 32 (dense desktop)")
val ff = desktop_ff()
val root = adaptive_nav_scaffold("nav_desk2", make_items(), make_content(), ff)
val home_btn = root.find_by_id("home")
expect(home_btn != nil).to_equal(true)
expect(home_btn.get_prop("min_height")).to_equal("32")
```

</details>

### adaptive_nav_scaffold resize re-selection

#### 390x844 → bottom, then 1440x900 → sidebar (pure function)

- 390x844 → bottom, then 1440x900 → sidebar (pure function)
   - Expected: root_phone.get_prop("nav_pattern") equals `bottom`
   - Expected: root_desktop.get_prop("nav_pattern") equals `sidebar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("390x844 → bottom, then 1440x900 → sidebar (pure function)")
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

- 1440x900 macos Expanded → list_detail == two_pane with both children
   - Expected: root.get_prop("list_detail") equals `two_pane`
   - Expected: all_ids contains `list_pane`
   - Expected: all_ids contains `detail_pane`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1440x900 macos Expanded → list_detail == two_pane with both children")
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

- 390x844 ios show_detail=false → list_detail == single_list, detail absent
   - Expected: root.get_prop("list_detail") equals `single_list`
   - Expected: all_ids contains `list_pane`
   - Expected: all_ids does not contain `detail_pane`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("390x844 ios show_detail=false → list_detail == single_list, detail absent")
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

- 390x844 ios show_detail=true → list_detail == single_detail, list absent
   - Expected: root.get_prop("list_detail") equals `single_detail`
   - Expected: all_ids contains `detail_pane`
   - Expected: all_ids does not contain `list_pane`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("390x844 ios show_detail=true → list_detail == single_detail, list absent")
val ff = phone_portrait_ff()
val root = list_detail_scaffold("ld_phone_detail", make_list_node(), make_detail_node(), ff, true)
expect(root.get_prop("list_detail")).to_equal("single_detail")
val all_ids = root.collect_ids()
expect(all_ids.contains("detail_pane")).to_equal(true)
expect(all_ids.contains("list_pane")).to_equal(false)
```

</details>

#### single_detail has back_nav=true on detail node

- single_detail has back_nav=true on detail node
   - Expected: detail != nil is true
   - Expected: detail.get_prop("back_nav") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single_detail has back_nav=true on detail node")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering adaptive_nav_scaffold phone portrait, adaptive_nav_scaffold landscape phone, adaptive_nav_scaffold tablet landscape, adaptive_nav_scaffold tablet portrait 700x1000 android Regular, adaptive_nav_scaffold desktop, adaptive_nav_scaffold resize re-selection, list_detail_scaffold desktop two_pane, list_detail_scaffold phone single_list, list_detail_scaffold phone single_detail.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `96d9a2723a8cf103f5d7e3b9bea9ab00a70def2f4b119ab5d648b2dcb16a0cb2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `96d9a2723a8cf103f5d7e3b9bea9ab00a70def2f4b119ab5d648b2dcb16a0cb2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `96d9a2723a8cf103f5d7e3b9bea9ab00a70def2f4b119ab5d648b2dcb16a0cb2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/adaptive_scaffold_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/adaptive_scaffold_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/adaptive_scaffold_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/adaptive_scaffold_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/adaptive_scaffold_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'nav_pattern prop == bottom' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/adaptive_scaffold_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'root is a column layout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/adaptive_scaffold_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'nav bar contains all 4 item ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
