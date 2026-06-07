# UI Lint Rules Specification

> Tests the Phase 8 UI lint rules exercised directly via `Linter` check methods.

<!-- sdn-diagram:id=lint_ui_rules_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lint_ui_rules_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lint_ui_rules_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lint_ui_rules_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# UI Lint Rules Specification

Tests the Phase 8 UI lint rules exercised directly via `Linter` check methods.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #UI001 #UI002 #UI003 |
| Category | Tooling / Lint |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/compiler/lint_ui_rules_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the Phase 8 UI lint rules exercised directly via `Linter` check methods.

## Key Concepts

| Concept | Description |
|---------|-------------|
| UI001 | Raw string literal as second arg of WidgetNode.new() |
| UI002 | Raw string literal in action pos of with_on_typed_action() or toast() |
| UI003 | Raw theme-name string literal not in an allowlisted file |
| Allowlist | Paths matching certain patterns are exempt from each rule |

## Scenarios

### UI001 — ui_no_raw_widget_kind

#### fires when second arg of WidgetNode.new is a string literal

1. var linter = Linter new
2. "val x = WidgetNode new
   - Expected: linter.results.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_widget_kind("/tmp/fake.spl",
    "val x = WidgetNode.new(\"root\", \"panel\")\n")
expect(linter.results.len()).to_equal(1)
```

</details>

#### result carries code UI001

1. var linter = Linter new
2. "val x = WidgetNode new
   - Expected: code equals `UI001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_widget_kind("/tmp/fake.spl",
    "val x = WidgetNode.new(\"root\", \"panel\")\n")
val code = linter.results[0].lint.code
expect(code).to_equal("UI001")
```

</details>

#### does not fire when kind is a variable (not a string literal)

1. var linter = Linter new
2. "val x = WidgetNode new
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_widget_kind("/tmp/fake.spl",
    "val x = WidgetNode.new(\"root\", my_kind)\n")
expect(linter.results.len()).to_equal(0)
```

</details>

#### does not fire on allowlisted parse path

1. var linter = Linter new
2. "val x = WidgetNode new
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_widget_kind(
    "src/lib/common/ui/parse/sdn_tree.spl",
    "val x = WidgetNode.new(\"root\", \"panel\")\n")
expect(linter.results.len()).to_equal(0)
```

</details>

#### does not fire on allowlisted builder path

1. var linter = Linter new
2. "val x = WidgetNode new
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_widget_kind(
    "src/lib/common/ui/builder.spl",
    "val x = WidgetNode.new(\"root\", \"panel\")\n")
expect(linter.results.len()).to_equal(0)
```

</details>

#### fires once per offending line (two offending lines → two results)

1. var linter = Linter new
2. "val a = WidgetNode new
   - Expected: linter.results.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_widget_kind("/tmp/fake.spl",
    "val a = WidgetNode.new(\"id1\", \"panel\")\nval b = WidgetNode.new(\"id2\", \"button\")\n")
expect(linter.results.len()).to_equal(2)
```

</details>

### UI002 — ui_no_raw_variant (with_on_typed_action)

#### fires when second arg of with_on_typed_action is a string literal

1. var linter = Linter new
2. "val w = with on typed action
   - Expected: linter.results.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_variant("/tmp/fake.spl",
    "val w = with_on_typed_action(node, \"save\")\n")
expect(linter.results.len()).to_equal(1)
```

</details>

#### result carries code UI002

1. var linter = Linter new
2. "val w = with on typed action
   - Expected: code equals `UI002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_variant("/tmp/fake.spl",
    "val w = with_on_typed_action(node, \"save\")\n")
val code = linter.results[0].lint.code
expect(code).to_equal("UI002")
```

</details>

#### does not fire when second arg is a typed action (no literal)

1. var linter = Linter new
2. "val w = with on typed action
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_variant("/tmp/fake.spl",
    "val w = with_on_typed_action(node, CommonAction.Save.into_action())\n")
expect(linter.results.len()).to_equal(0)
```

</details>

#### does not fire on allowlisted builder path

1. var linter = Linter new
2. "val w = with on typed action
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_variant(
    "src/lib/common/ui/builder.spl",
    "val w = with_on_typed_action(node, \"save\")\n")
expect(linter.results.len()).to_equal(0)
```

</details>

#### does not fire on allowlisted glass/builder path

1. var linter = Linter new
2. "val w = with on typed action
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_variant(
    "src/lib/common/ui/glass/builder.spl",
    "val w = with_on_typed_action(node, \"save\")\n")
expect(linter.results.len()).to_equal(0)
```

</details>

### UI002 — ui_no_raw_variant (toast)

#### fires when third arg of toast is a string literal

1. var linter = Linter new
2. "toast
   - Expected: linter.results.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_variant("/tmp/fake.spl",
    "toast(node, msg, \"success\")\n")
expect(linter.results.len()).to_equal(1)
```

</details>

#### result carries code UI002 for toast

1. var linter = Linter new
2. "toast
   - Expected: code equals `UI002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_variant("/tmp/fake.spl",
    "toast(node, msg, \"success\")\n")
val code = linter.results[0].lint.code
expect(code).to_equal("UI002")
```

</details>

#### does not fire when toast variant is a variable

1. var linter = Linter new
2. "toast
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_variant("/tmp/fake.spl",
    "toast(node, msg, variant)\n")
expect(linter.results.len()).to_equal(0)
```

</details>

### UI003 — ui_no_raw_theme_name

#### fires on raw ios_light theme string

1. var linter = Linter new
2. "val t = theme by name
   - Expected: linter.results.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_theme_name("/tmp/fake.spl",
    "val t = theme_by_name(\"ios_light\")\n")
expect(linter.results.len()).to_equal(1)
```

</details>

#### result carries code UI003

1. var linter = Linter new
2. "val t = theme by name
   - Expected: code equals `UI003`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_theme_name("/tmp/fake.spl",
    "val t = theme_by_name(\"ios_light\")\n")
val code = linter.results[0].lint.code
expect(code).to_equal("UI003")
```

</details>

#### fires on glass_obsidian_dark theme string

1. var linter = Linter new
   - Expected: linter.results.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_theme_name("/tmp/fake.spl",
    "val t = \"glass_obsidian_dark\"\n")
expect(linter.results.len()).to_equal(1)
```

</details>

#### fires on simple_dark theme string

1. var linter = Linter new
   - Expected: linter.results.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_theme_name("/tmp/fake.spl",
    "val t = \"simple_dark\"\n")
expect(linter.results.len()).to_equal(1)
```

</details>

#### does not fire on non-theme string

1. var linter = Linter new
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_theme_name("/tmp/fake.spl",
    "val t = \"some_other_value\"\n")
expect(linter.results.len()).to_equal(0)
```

</details>

#### does not fire on allowlisted style.spl path

1. var linter = Linter new
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_theme_name(
    "src/lib/common/ui/style.spl",
    "val t = \"ios_light\"\n")
expect(linter.results.len()).to_equal(0)
```

</details>

#### does not fire on comment lines

1. var linter = Linter new
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_theme_name("/tmp/fake.spl",
    "# use ios_light for testing\n")
expect(linter.results.len()).to_equal(0)
```

</details>

#### does not fire when theme name appears unquoted

1. var linter = Linter new
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
linter.check_ui_raw_theme_name("/tmp/fake.spl",
    "val t = ios_light\n")
expect(linter.results.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
