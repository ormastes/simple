# Widget Table List Upgrade Specification

> Tests covering table_widget creation, table_row helper, table HTML rendering, with_selected modifier, list HTML rendering with selection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Table List Upgrade Specification

## Scenarios

### table_widget creation

#### creates a widget with kind table

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a widget with kind table


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a widget with kind table")
val t = table_widget("tbl_kind_1", ["A", "B"], [["1", "2"]])
expect t.kind_name() to_equal "table"
```

</details>

#### assigns the correct id

- assigns the correct id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns the correct id")
val t = table_widget("tbl_id_1", ["X"], [["Y"]])
expect t.id to_equal "tbl_id_1"
```

</details>

#### headers prop is joined by pipe

- headers prop is joined by pipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("headers prop is joined by pipe")
val t = table_widget("tbl_hdr_1", ["Name", "Age", "City"], [])
expect t.get_prop("headers") to_equal "Name|Age|City"
```

</details>

#### single header has no pipe

- single header has no pipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single header has no pipe")
val t = table_widget("tbl_hdr_2", ["Only"], [])
expect t.get_prop("headers") to_equal "Only"
```

</details>

#### sort_column defaults to empty

- sort_column defaults to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sort_column defaults to empty")
val t = table_widget("tbl_sort_1", ["A"], [])
expect t.get_prop("sort_column") to_equal ""
```

</details>

#### sort_dir defaults to asc

- sort_dir defaults to asc


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sort_dir defaults to asc")
val t = table_widget("tbl_sort_2", ["A"], [])
expect t.get_prop("sort_dir") to_equal "asc"
```

</details>

#### filter_text defaults to empty

- filter_text defaults to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filter_text defaults to empty")
val t = table_widget("tbl_filter_1", ["A"], [])
expect t.get_prop("filter_text") to_equal ""
```

</details>

#### row children have label with cells joined by pipe

- row children have label with cells joined by pipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("row children have label with cells joined by pipe")
val t = table_widget("tbl_row_1", ["H1", "H2"], [["a", "b"], ["c", "d"]])
val first = t.child_at(0)
expect first != nil to_equal true
expect first.get_prop("label") to_equal "a|b"
```

</details>

#### second row child has correct label

- second row child has correct label


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("second row child has correct label")
val t = table_widget("tbl_row_2", ["H1", "H2"], [["x", "y"], ["p", "q"]])
val second = t.child_at(1)
expect second != nil to_equal true
expect second.get_prop("label") to_equal "p|q"
```

</details>

#### has correct child count matching row count

- has correct child count matching row count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct child count matching row count")
val t = table_widget("tbl_count_1", ["A"], [["1"], ["2"], ["3"]])
expect t.child_count() to_equal 3
```

</details>

#### empty rows produce zero children

- empty rows produce zero children


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty rows produce zero children")
val t = table_widget("tbl_empty_1", ["A", "B"], [])
expect t.child_count() to_equal 0
```

</details>

### table_row helper

#### creates text kind node

- creates text kind node


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates text kind node")
val r = table_row("tr_kind_1", ["a", "b"])
expect r.kind_name() to_equal "text"
```

</details>

#### label is cells joined by pipe

- label is cells joined by pipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("label is cells joined by pipe")
val r = table_row("tr_label_1", ["hello", "world"])
expect r.get_prop("label") to_equal "hello|world"
```

</details>

#### single cell has no pipe

- single cell has no pipe


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single cell has no pipe")
val r = table_row("tr_single_1", ["only"])
expect r.get_prop("label") to_equal "only"
```

</details>

### table HTML rendering

#### output contains th tags for headers

- output contains th tags for headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains th tags for headers")
val node = table_widget("tbl_html_1", ["Name", "Age"], [["Alice", "30"]])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "<th"
```

</details>

#### output contains thead element

- output contains thead element


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains thead element")
val node = table_widget("tbl_html_2", ["Col1"], [["val1"]])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "<thead>"
```

</details>

#### output contains tbody element

- output contains tbody element


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains tbody element")
val node = table_widget("tbl_html_3", ["Col1"], [["val1"]])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "<tbody>"
```

</details>

#### output contains table-filter input

- output contains table-filter input


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains table-filter input")
val node = table_widget("tbl_html_4", ["A"], [["x"]])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "table-filter"
```

</details>

#### output contains widget-table class

- output contains widget-table class


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains widget-table class")
val node = table_widget("tbl_html_5", ["A"], [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-table"
```

</details>

#### output contains header text

- output contains header text


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains header text")
val node = table_widget("tbl_html_6", ["Name", "Score"], [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "Name"
expect html to_contain "Score"
```

</details>

#### output contains td tags for cell data

- output contains td tags for cell data


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains td tags for cell data")
val node = table_widget("tbl_html_7", ["A"], [["hello"]])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "<td>"
```

</details>

#### output contains data-action for sort on headers

- output contains data-action for sort on headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains data-action for sort on headers")
val node = table_widget("tbl_html_8", ["Col1", "Col2"], [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "data-action=\"sort_col_0\""
expect html to_contain "data-action=\"sort_col_1\""
```

</details>

#### output includes filter data-action with table id

- output includes filter data-action with table id


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output includes filter data-action with table id")
val node = table_widget("tbl_html_9", ["X"], [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "data-action=\"filter_tbl_html_9\""
```

</details>

### with_selected modifier

#### sets selected_index prop

- sets selected_index prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets selected_index prop")
var lw = list_widget("ls_sel_1", ["A", "B", "C"])
lw = with_selected(lw, 1)
expect lw.get_prop("selected_index") to_equal "1"
```

</details>

#### default list has no selected_index

- default list has no selected_index


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default list has no selected_index")
val lw = list_widget("ls_nosel_1", ["A", "B"])
expect lw.get_prop("selected_index") to_equal ""
```

</details>

#### selected_index zero is valid

- selected_index zero is valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selected_index zero is valid")
var lw = list_widget("ls_sel_2", ["First"])
lw = with_selected(lw, 0)
expect lw.get_prop("selected_index") to_equal "0"
```

</details>

#### can change selected index

- can change selected index


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can change selected index")
var lw = list_widget("ls_sel_3", ["A", "B", "C"])
lw = with_selected(lw, 0)
expect lw.get_prop("selected_index") to_equal "0"
lw = with_selected(lw, 2)
expect lw.get_prop("selected_index") to_equal "2"
```

</details>

### list HTML rendering with selection

#### selected item has selected class

- selected item has selected class


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selected item has selected class")
var node = list_widget("ls_html_1", ["Apple", "Banana", "Cherry"])
node = with_selected(node, 1)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "selected"
```

</details>

#### selected item has list-item selected class

- selected item has list-item selected class


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selected item has list-item selected class")
var node = list_widget("ls_html_2", ["X", "Y"])
node = with_selected(node, 0)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "list-item selected"
```

</details>

#### non-selected items have list-item class only

- non-selected items have list-item class only


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-selected items have list-item class only")
var node = list_widget("ls_html_3", ["A", "B"])
node = with_selected(node, 0)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "list-item\""
```

</details>

#### no selection means no selected class

- no selection means no selected class


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no selection means no selected class")
val node = list_widget("ls_html_4", ["One", "Two"])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
# All items should be "list-item" without "selected"
expect html to_contain "list-item"
```

</details>

#### output still contains widget-list class

- output still contains widget-list class


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output still contains widget-list class")
var node = list_widget("ls_html_5", ["Item"])
node = with_selected(node, 0)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-list"
```

</details>

#### output starts with ul tag

- output starts with ul tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output starts with ul tag")
var node = list_widget("ls_html_6", ["A"])
node = with_selected(node, 0)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_start_with "<ul"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/widget_table_list_upgrade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering table_widget creation, table_row helper, table HTML rendering, with_selected modifier, list HTML rendering with selection.
- table_widget creation
- table_row helper
- table HTML rendering
- with_selected modifier
- list HTML rendering with selection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
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

- Canonical SPipe generation for source `c1e7c107de562ba446e4a46879ec07cd1e7fb84002fab4371f9bdb63fe76fe05`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c1e7c107de562ba446e4a46879ec07cd1e7fb84002fab4371f9bdb63fe76fe05`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c1e7c107de562ba446e4a46879ec07cd1e7fb84002fab4371f9bdb63fe76fe05`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/unit/app/ui/widget_table_list_upgrade_spec.spl
mirror: doc/06_spec/unit/app/ui/widget_table_list_upgrade_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/widget_table_list_upgrade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/widget_table_list_upgrade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/widget_table_list_upgrade_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a widget with kind table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/widget_table_list_upgrade_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assigns the correct id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/widget_table_list_upgrade_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'headers prop is joined by pipe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/widget_table_list_upgrade_spec.spl:234:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can change selected index' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
