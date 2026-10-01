# UI Lint Rules Specification

> Purpose: Prove that UI001 — ui_no_raw_widget_kind.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# UI Lint Rules Specification

Purpose: Prove that UI001 — ui_no_raw_widget_kind.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that UI001 — ui_no_raw_widget_kind.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### UI001 — ui_no_raw_widget_kind

#### fires when second arg of WidgetNode.new is a string literal

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fires when second arg of WidgetNode.new is a string literal
- Verify: fires when second arg of WidgetNode.new is a string literal
   - Expected: linter.results.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fires when second arg of WidgetNode.new is a string literal")
step("Verify: fires when second arg of WidgetNode.new is a string literal")
# @req: REQ-COMP-UI001-UI-NO-RAW-WIDGET-KIND-001
var linter = Linter.new()
linter.check_ui_raw_widget_kind("/tmp/fake.spl",
    "val x = WidgetNode.new(\"root\", \"panel\")\n")
expect(linter.results.len()).to_equal(1)
```

</details>

#### result carries code UI001

- result carries code UI001
- Verify: result carries code UI001
   - Expected: code equals `UI001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("result carries code UI001")
step("Verify: result carries code UI001")
var linter = Linter.new()
linter.check_ui_raw_widget_kind("/tmp/fake.spl",
    "val x = WidgetNode.new(\"root\", \"panel\")\n")
val code = linter.results[0].lint.code
expect(code).to_equal("UI001")
```

</details>

#### does not fire when kind is a variable (not a string literal)

- does not fire when kind is a variable (not a string literal)
- Verify: does not fire when kind is a variable (not a string literal)
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not fire when kind is a variable (not a string literal)")
step("Verify: does not fire when kind is a variable (not a string literal)")
var linter = Linter.new()
linter.check_ui_raw_widget_kind("/tmp/fake.spl",
    "val x = WidgetNode.new(\"root\", my_kind)\n")
expect(linter.results.len()).to_equal(0)
```

</details>

#### does not fire on allowlisted parse path

- does not fire on allowlisted parse path
- Verify: does not fire on allowlisted parse path
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not fire on allowlisted parse path")
step("Verify: does not fire on allowlisted parse path")
var linter = Linter.new()
linter.check_ui_raw_widget_kind(
    "src/lib/common/ui/parse/sdn_tree.spl",
    "val x = WidgetNode.new(\"root\", \"panel\")\n")
expect(linter.results.len()).to_equal(0)
```

</details>

#### does not fire on allowlisted builder path

- does not fire on allowlisted builder path
- Verify: does not fire on allowlisted builder path
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not fire on allowlisted builder path")
step("Verify: does not fire on allowlisted builder path")
var linter = Linter.new()
linter.check_ui_raw_widget_kind(
    "src/lib/common/ui/builder.spl",
    "val x = WidgetNode.new(\"root\", \"panel\")\n")
expect(linter.results.len()).to_equal(0)
```

</details>

#### fires once per offending line (two offending lines → two results)

- fires once per offending line (two offending lines → two results)
- Verify: fires once per offending line (two offending lines → two results)
   - Expected: linter.results.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fires once per offending line (two offending lines → two results)")
step("Verify: fires once per offending line (two offending lines → two results)")
var linter = Linter.new()
linter.check_ui_raw_widget_kind("/tmp/fake.spl",
    "val a = WidgetNode.new(\"id1\", \"panel\")\nval b = WidgetNode.new(\"id2\", \"button\")\n")
expect(linter.results.len()).to_equal(2)
```

</details>

### UI002 — ui_no_raw_variant (with_on_typed_action)

#### fires when second arg of with_on_typed_action is a string literal

- fires when second arg of with_on_typed_action is a string literal
- Verify: fires when second arg of with_on_typed_action is a string literal
   - Expected: linter.results.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fires when second arg of with_on_typed_action is a string literal")
step("Verify: fires when second arg of with_on_typed_action is a string literal")
var linter = Linter.new()
linter.check_ui_raw_variant("/tmp/fake.spl",
    "val w = with_on_typed_action(node, \"save\")\n")
expect(linter.results.len()).to_equal(1)
```

</details>

#### result carries code UI002

- result carries code UI002
- Verify: result carries code UI002
   - Expected: code equals `UI002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("result carries code UI002")
step("Verify: result carries code UI002")
var linter = Linter.new()
linter.check_ui_raw_variant("/tmp/fake.spl",
    "val w = with_on_typed_action(node, \"save\")\n")
val code = linter.results[0].lint.code
expect(code).to_equal("UI002")
```

</details>

#### does not fire when second arg is a typed action (no literal)

- does not fire when second arg is a typed action (no literal)
- Verify: does not fire when second arg is a typed action (no literal)
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not fire when second arg is a typed action (no literal)")
step("Verify: does not fire when second arg is a typed action (no literal)")
var linter = Linter.new()
linter.check_ui_raw_variant("/tmp/fake.spl",
    "val w = with_on_typed_action(node, CommonAction.Save.into_action())\n")
expect(linter.results.len()).to_equal(0)
```

</details>

#### does not fire on allowlisted builder path

- does not fire on allowlisted builder path
- Verify: does not fire on allowlisted builder path
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not fire on allowlisted builder path")
step("Verify: does not fire on allowlisted builder path")
var linter = Linter.new()
linter.check_ui_raw_variant(
    "src/lib/common/ui/builder.spl",
    "val w = with_on_typed_action(node, \"save\")\n")
expect(linter.results.len()).to_equal(0)
```

</details>

#### does not fire on allowlisted glass/builder path

- does not fire on allowlisted glass/builder path
- Verify: does not fire on allowlisted glass/builder path
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not fire on allowlisted glass/builder path")
step("Verify: does not fire on allowlisted glass/builder path")
var linter = Linter.new()
linter.check_ui_raw_variant(
    "src/lib/common/ui/glass/builder.spl",
    "val w = with_on_typed_action(node, \"save\")\n")
expect(linter.results.len()).to_equal(0)
```

</details>

### UI002 — ui_no_raw_variant (toast)

#### fires when third arg of toast is a string literal

- fires when third arg of toast is a string literal
- Verify: fires when third arg of toast is a string literal
   - Expected: linter.results.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fires when third arg of toast is a string literal")
step("Verify: fires when third arg of toast is a string literal")
var linter = Linter.new()
linter.check_ui_raw_variant("/tmp/fake.spl",
    "toast(node, msg, \"success\")\n")
expect(linter.results.len()).to_equal(1)
```

</details>

#### result carries code UI002 for toast

- result carries code UI002 for toast
- Verify: result carries code UI002 for toast
   - Expected: code equals `UI002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("result carries code UI002 for toast")
step("Verify: result carries code UI002 for toast")
var linter = Linter.new()
linter.check_ui_raw_variant("/tmp/fake.spl",
    "toast(node, msg, \"success\")\n")
val code = linter.results[0].lint.code
expect(code).to_equal("UI002")
```

</details>

#### does not fire when toast variant is a variable

- does not fire when toast variant is a variable
- Verify: does not fire when toast variant is a variable
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not fire when toast variant is a variable")
step("Verify: does not fire when toast variant is a variable")
var linter = Linter.new()
linter.check_ui_raw_variant("/tmp/fake.spl",
    "toast(node, msg, variant)\n")
expect(linter.results.len()).to_equal(0)
```

</details>

### UI003 — ui_no_raw_theme_name

#### fires on raw ios_light theme string

- fires on raw ios_light theme string
- Verify: fires on raw ios_light theme string
   - Expected: linter.results.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fires on raw ios_light theme string")
step("Verify: fires on raw ios_light theme string")
var linter = Linter.new()
linter.check_ui_raw_theme_name("/tmp/fake.spl",
    "val t = theme_by_name(\"ios_light\")\n")
expect(linter.results.len()).to_equal(1)
```

</details>

#### result carries code UI003

- result carries code UI003
- Verify: result carries code UI003
   - Expected: code equals `UI003`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("result carries code UI003")
step("Verify: result carries code UI003")
var linter = Linter.new()
linter.check_ui_raw_theme_name("/tmp/fake.spl",
    "val t = theme_by_name(\"ios_light\")\n")
val code = linter.results[0].lint.code
expect(code).to_equal("UI003")
```

</details>

#### fires on glass_obsidian_dark theme string

- fires on glass_obsidian_dark theme string
- Verify: fires on glass_obsidian_dark theme string
   - Expected: linter.results.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fires on glass_obsidian_dark theme string")
step("Verify: fires on glass_obsidian_dark theme string")
var linter = Linter.new()
linter.check_ui_raw_theme_name("/tmp/fake.spl",
    "val t = \"glass_obsidian_dark\"\n")
expect(linter.results.len()).to_equal(1)
```

</details>

#### fires on simple_dark theme string

- fires on simple_dark theme string
- Verify: fires on simple_dark theme string
   - Expected: linter.results.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fires on simple_dark theme string")
step("Verify: fires on simple_dark theme string")
var linter = Linter.new()
linter.check_ui_raw_theme_name("/tmp/fake.spl",
    "val t = \"simple_dark\"\n")
expect(linter.results.len()).to_equal(1)
```

</details>

#### does not fire on non-theme string

- does not fire on non-theme string
- Verify: does not fire on non-theme string
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not fire on non-theme string")
step("Verify: does not fire on non-theme string")
var linter = Linter.new()
linter.check_ui_raw_theme_name("/tmp/fake.spl",
    "val t = \"some_other_value\"\n")
expect(linter.results.len()).to_equal(0)
```

</details>

#### does not fire on allowlisted style.spl path

- does not fire on allowlisted style.spl path
- Verify: does not fire on allowlisted style.spl path
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not fire on allowlisted style.spl path")
step("Verify: does not fire on allowlisted style.spl path")
var linter = Linter.new()
linter.check_ui_raw_theme_name(
    "src/lib/common/ui/style.spl",
    "val t = \"ios_light\"\n")
expect(linter.results.len()).to_equal(0)
```

</details>

#### does not fire on comment lines

- does not fire on comment lines
- Verify: does not fire on comment lines
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not fire on comment lines")
step("Verify: does not fire on comment lines")
var linter = Linter.new()
linter.check_ui_raw_theme_name("/tmp/fake.spl",
    "# use ios_light for testing\n")
expect(linter.results.len()).to_equal(0)
```

</details>

#### does not fire when theme name appears unquoted

- does not fire when theme name appears unquoted
- Verify: does not fire when theme name appears unquoted
   - Expected: linter.results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not fire when theme name appears unquoted")
step("Verify: does not fire when theme name appears unquoted")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-UI001-UI-NO-RAW-WIDGET-KIND-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7b801e44a4fb806346b6f097cf64a7252e14b8399daa1cfc6717aa8645851946`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7b801e44a4fb806346b6f097cf64a7252e14b8399daa1cfc6717aa8645851946`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7b801e44a4fb806346b6f097cf64a7252e14b8399daa1cfc6717aa8645851946`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/lint_ui_rules_spec.spl
mirror: doc/06_spec/01_unit/compiler/lint_ui_rules_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lint_ui_rules_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lint_ui_rules_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lint_ui_rules_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 18 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/lint_ui_rules_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fires when second arg of WidgetNode.new is a string literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint_ui_rules_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'result carries code UI001' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint_ui_rules_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not fire when kind is a variable (not a string literal)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
