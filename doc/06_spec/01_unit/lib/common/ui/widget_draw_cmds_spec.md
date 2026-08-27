# Widget Draw Cmds Specification

> Tests covering widget_draw_cmds non-empty — phone, widget_draw_cmds non-empty — tablet, widget_draw_cmds non-empty — desktop, widget_draw_cmds phone bottom bar position, widget_draw_cmds tablet rail position, widget_draw_cmds desktop sidebar width, widget_draw_cmds nav_pattern_probe labels.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Draw Cmds Specification

## Scenarios

### widget_draw_cmds non-empty — phone

#### cmds non-empty at 390x844

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- cmds non-empty at 390x844
   - Expected: cmds.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cmds non-empty at 390x844")
val root = phone_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 390, 844)
expect(cmds.len() > 0).to_equal(true)
```

</details>

#### contains cmd for nav_home at 390x844

- contains cmd for nav_home at 390x844
   - Expected: cmd != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains cmd for nav_home at 390x844")
val root = phone_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 390, 844)
val cmd = find_cmd_for(cmds, "nav_home")
expect(cmd != nil).to_equal(true)
```

</details>

### widget_draw_cmds non-empty — tablet

#### cmds non-empty at 700x1000

- cmds non-empty at 700x1000
   - Expected: cmds.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cmds non-empty at 700x1000")
val root = tablet_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 700, 1000)
expect(cmds.len() > 0).to_equal(true)
```

</details>

#### contains cmd for nav_home at 700x1000

- contains cmd for nav_home at 700x1000
   - Expected: cmd != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains cmd for nav_home at 700x1000")
val root = tablet_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 700, 1000)
val cmd = find_cmd_for(cmds, "nav_home")
expect(cmd != nil).to_equal(true)
```

</details>

### widget_draw_cmds non-empty — desktop

#### cmds non-empty at 1440x900

- cmds non-empty at 1440x900
   - Expected: cmds.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cmds non-empty at 1440x900")
val root = desktop_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 1440, 900)
expect(cmds.len() > 0).to_equal(true)
```

</details>

#### contains cmd for nav_home at 1440x900

- contains cmd for nav_home at 1440x900
   - Expected: cmd != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains cmd for nav_home at 1440x900")
val root = desktop_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 1440, 900)
val cmd = find_cmd_for(cmds, "nav_home")
expect(cmd != nil).to_equal(true)
```

</details>

### widget_draw_cmds phone bottom bar position

#### nav_home cmd y > 422 (below mid-screen, bottom bar)

- nav_home cmd y > 422 (below mid-screen, bottom bar)
   - Expected: cmd != nil is true
   - Expected: cmd.y > 422 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nav_home cmd y > 422 (below mid-screen, bottom bar)")
val root = phone_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 390, 844)
val cmd = find_cmd_for(cmds, "nav_home")
expect(cmd != nil).to_equal(true)
expect(cmd.y > 422).to_equal(true)
```

</details>

### widget_draw_cmds tablet rail position

#### nav_home cmd x < 100 (left rail)

- nav_home cmd x < 100 (left rail)
   - Expected: cmd != nil is true
   - Expected: cmd.x < 100 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nav_home cmd x < 100 (left rail)")
val root = tablet_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 700, 1000)
val cmd = find_cmd_for(cmds, "nav_home")
expect(cmd != nil).to_equal(true)
expect(cmd.x < 100).to_equal(true)
```

</details>

#### tablet_root_nav_rail container rect w < 120

- tablet_root_nav_rail container rect w < 120
   - Expected: rail_cmd != nil is true
   - Expected: rail_cmd.w < 120 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tablet_root_nav_rail container rect w < 120")
val root = tablet_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 700, 1000)
val rail_cmd = find_rect_for(cmds, "tablet_root_nav_rail")
expect(rail_cmd != nil).to_equal(true)
expect(rail_cmd.w < 120).to_equal(true)
```

</details>

### widget_draw_cmds desktop sidebar width

#### desktop_root_nav_sidebar container rect w >= 200

- desktop_root_nav_sidebar container rect w >= 200
   - Expected: sidebar_cmd != nil is true
   - Expected: sidebar_cmd.w >= 200 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("desktop_root_nav_sidebar container rect w >= 200")
val root = desktop_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 1440, 900)
val sidebar_cmd = find_rect_for(cmds, "desktop_root_nav_sidebar")
expect(sidebar_cmd != nil).to_equal(true)
expect(sidebar_cmd.w >= 200).to_equal(true)
```

</details>

### widget_draw_cmds nav_pattern_probe labels

#### phone probe label == bottom

- phone probe label == bottom
   - Expected: probe != nil is true
   - Expected: probe.label equals `bottom`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("phone probe label == bottom")
val root = phone_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 390, 844)
val probe = find_probe(cmds)
expect(probe != nil).to_equal(true)
expect(probe.label).to_equal("bottom")
```

</details>

#### tablet probe label == rail

- tablet probe label == rail
   - Expected: probe != nil is true
   - Expected: probe.label equals `rail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tablet probe label == rail")
val root = tablet_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 700, 1000)
val probe = find_probe(cmds)
expect(probe != nil).to_equal(true)
expect(probe.label).to_equal("rail")
```

</details>

#### desktop probe label == sidebar

- desktop probe label == sidebar
   - Expected: probe != nil is true
   - Expected: probe.label equals `sidebar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("desktop probe label == sidebar")
val root = desktop_scaffold()
val cmds = widget_tree_to_draw_cmds(root, 1440, 900)
val probe = find_probe(cmds)
expect(probe != nil).to_equal(true)
expect(probe.label).to_equal("sidebar")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/widget_draw_cmds_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering widget_draw_cmds non-empty — phone, widget_draw_cmds non-empty — tablet, widget_draw_cmds non-empty — desktop, widget_draw_cmds phone bottom bar position, widget_draw_cmds tablet rail position, widget_draw_cmds desktop sidebar width, widget_draw_cmds nav_pattern_probe labels.
- widget_draw_cmds non-empty — phone
- widget_draw_cmds non-empty — tablet
- widget_draw_cmds non-empty — desktop
- widget_draw_cmds phone bottom bar position
- widget_draw_cmds tablet rail position
- widget_draw_cmds desktop sidebar width
- widget_draw_cmds nav_pattern_probe labels

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `9dcb9fdd5365dfe6bdfe770d50239487ad91bf516459936eebf4545d4a1f19d5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9dcb9fdd5365dfe6bdfe770d50239487ad91bf516459936eebf4545d4a1f19d5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9dcb9fdd5365dfe6bdfe770d50239487ad91bf516459936eebf4545d4a1f19d5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/widget_draw_cmds_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/widget_draw_cmds_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/widget_draw_cmds_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/widget_draw_cmds_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/widget_draw_cmds_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cmds non-empty at 390x844' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/widget_draw_cmds_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains cmd for nav_home at 390x844' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/widget_draw_cmds_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cmds non-empty at 700x1000' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
