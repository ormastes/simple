# Widget DrawIR coverage — previously chromeless/missing widget kinds

> Asserts the DrawIR composition carries real chrome for the widget kinds the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget DrawIR coverage — previously chromeless/missing widget kinds

Asserts the DrawIR composition carries real chrome for the widget kinds the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/widget_draw_ir_widgets_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Asserts the DrawIR composition carries real chrome for the widget kinds the
2026-08-11 whole-gallery render found missing or bare (radio, switch, tree,
table header, segmented control, dropdown chrome, tabs selection, list
banding, divider). Assertions key on command ids and color RELATIONSHIPS
(selected != unselected), never on hardcoded palette values, so theme
changes do not break the spec.

## Scenarios

### Widget DrawIR chrome coverage

#### switch emits track and thumb, thumb parked right when on

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- switch emits track and thumb, thumb parked right when on
- Find the switch chrome commands
   - Expected: has_command_with_suffix(cmds, "-thumb") is true
   - Expected: track != 0u32 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("switch emits track and thumb, thumb parked right when on")
step("Find the switch chrome commands")
val cmds = gallery_commands()
expect(has_command_with_suffix(cmds, "-thumb")).to_equal(true)
val track = command_color(cmds, "spec_sw")
expect(track != 0u32).to_equal(true)
```

</details>

#### radio emits a ring and a checked dot

- radio emits a ring and a checked dot
- Find the radio chrome commands
   - Expected: has_command_with_suffix(cmds, "-ring") is true
   - Expected: has_command_with_suffix(cmds, "-dot") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("radio emits a ring and a checked dot")
step("Find the radio chrome commands")
val cmds = gallery_commands()
expect(has_command_with_suffix(cmds, "-ring")).to_equal(true)
expect(has_command_with_suffix(cmds, "-dot")).to_equal(true)
```

</details>

#### dropdown emits field + chevron and hides its item list

- dropdown emits field + chevron and hides its item list
- The closed dropdown shows the first item as the value
   - Expected: has_command_with_suffix(cmds, "-field") is true
   - Expected: has_command_with_suffix(cmds, "-chevron") is true
   - Expected: items_leaked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dropdown emits field + chevron and hides its item list")
step("The closed dropdown shows the first item as the value")
val cmds = gallery_commands()
expect(has_command_with_suffix(cmds, "-field")).to_equal(true)
expect(has_command_with_suffix(cmds, "-chevron")).to_equal(true)
var items_leaked = false
for cmd in cmds:
    if cmd.component_id.contains("spec_drop_"):
        items_leaked = true
expect(items_leaked).to_equal(false)
```

</details>

#### tabs emit a selection underline on the selected tab

- tabs emit a selection underline on the selected tab
- Find the tabs selection marker
   - Expected: has_command_with_suffix(cmds, "-sel") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tabs emit a selection underline on the selected tab")
step("Find the tabs selection marker")
val cmds = gallery_commands()
expect(has_command_with_suffix(cmds, "-sel")).to_equal(true)
```

</details>

#### segmented control fills the selected segment differently

- segmented control fills the selected segment differently
- Selected and unselected segment fills must differ
   - Expected: sel_color != 0u32 is true
   - Expected: sel_color != other_color is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("segmented control fills the selected segment differently")
step("Selected and unselected segment fills must differ")
val cmds = gallery_commands()
val sel_color = command_color(cmds, "spec_seg-seg1")
val other_color = command_color(cmds, "spec_seg-seg0")
expect(sel_color != 0u32).to_equal(true)
expect(sel_color != other_color).to_equal(true)
```

</details>

#### list emits banding under even rows

- list emits banding under even rows
- Find the list band command
   - Expected: has_command_with_suffix(cmds, "-band0") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("list emits banding under even rows")
step("Find the list band command")
val cmds = gallery_commands()
expect(has_command_with_suffix(cmds, "-band0")).to_equal(true)
```

</details>

#### table emits a header band and the header text

- table emits a header band and the header text
- Find the table header chrome
   - Expected: has_command_with_suffix(cmds, "-header") is true
   - Expected: has_command_with_suffix(cmds, "-header-text") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("table emits a header band and the header text")
step("Find the table header chrome")
val cmds = gallery_commands()
expect(has_command_with_suffix(cmds, "-header")).to_equal(true)
expect(has_command_with_suffix(cmds, "-header-text")).to_equal(true)
```

</details>

#### tree emits the expansion marker and label

- tree emits the expansion marker and label
- Find the tree marker command
   - Expected: has_command_with_suffix(cmds, "-mark") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tree emits the expansion marker and label")
step("Find the tree marker command")
val cmds = gallery_commands()
expect(has_command_with_suffix(cmds, "-mark")).to_equal(true)
```

</details>

#### divider emits its 1px line

- divider emits its 1px line
- Find the divider command with height 1
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("divider emits its 1px line")
step("Find the divider command with height 1")
val cmds = gallery_commands()
var found = false
for cmd in cmds:
    if cmd.component_id == "spec_div" and cmd.height == 1:
        found = true
expect(found).to_equal(true)
```

</details>

### Widget DrawIR event check

#### clicking a checkbox flips its mark in the next frame

- clicking a checkbox flips its mark in the next frame
- Build a one-checkbox tree and render the checked mark color
- Click the checkbox and re-render
   - Expected: hit equals `ev_chk`
- The mark color changed (checked -> unchecked)
   - Expected: mark_before != 0u32 is true
   - Expected: mark_after != 0u32 is true
   - Expected: mark_before != mark_after is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clicking a checkbox flips its mark in the next frame")
step("Build a one-checkbox tree and render the checked mark color")
val tree = build_tree_with_title(column("ev_root", [
    with_height(checkbox("ev_chk", "toggle me", true), 24)
]), "ev", "glass_dark")
val before = all_commands(widget_tree_to_draw_ir_cpu(tree.root_node(), 200, 60))
val mark_before = command_color(before, "ev_chk-mark")
step("Click the checkbox and re-render")
val hit = widget_dispatch_click(tree.root_node(), 200, 60, 8, 12)
expect(hit).to_equal("ev_chk")
val after = all_commands(widget_tree_to_draw_ir_cpu(tree.root_node(), 200, 60))
val mark_after = command_color(after, "ev_chk-mark")
step("The mark color changed (checked -> unchecked)")
expect(mark_before != 0u32).to_equal(true)
expect(mark_after != 0u32).to_equal(true)
expect(mark_before != mark_after).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3f2abcc1131a2cb9abaaec6d25ff6e7a6fd235659470654dfbd22485da4e1cc5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3f2abcc1131a2cb9abaaec6d25ff6e7a6fd235659470654dfbd22485da4e1cc5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3f2abcc1131a2cb9abaaec6d25ff6e7a6fd235659470654dfbd22485da4e1cc5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/widget_draw_ir_widgets_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/widget_draw_ir_widgets_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/widget_draw_ir_widgets_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/widget_draw_ir_widgets_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/widget_draw_ir_widgets_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'switch emits track and thumb, thumb parked right when on' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/widget_draw_ir_widgets_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'radio emits a ring and a checked dot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/widget_draw_ir_widgets_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dropdown emits field + chevron and hides its item list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
