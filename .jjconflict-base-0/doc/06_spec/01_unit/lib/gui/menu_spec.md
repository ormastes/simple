# Menu Specification

> Tests covering Menu.new, MenuItem kinds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Menu Specification

## Scenarios

### Menu.new

#### has 0 items

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has 0 items


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has 0 items")
val m = Menu.new(1)
expect m.item_count() to_equal 0
```

</details>

#### append bumps count

- append bumps count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("append bumps count")
var m = Menu.new(1)
m.append(_normal_item(1, "File"))
expect m.item_count() to_equal 1
```

</details>

#### append twice gives count 2

- append twice gives count 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("append twice gives count 2")
var m = Menu.new(1)
m.append(_normal_item(1, "File"))
m.append(_normal_item(2, "Edit"))
expect m.item_count() to_equal 2
```

</details>

### MenuItem kinds

#### Separator kind round-trips

- Separator kind round-trips


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Separator kind round-trips")
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

- accelerator text round-trips


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accelerator text round-trips")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Menu.new, MenuItem kinds.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fa929f54f211e1c98cfa837fbc26e90f55704709eb5e826a5c4f48d839a3c153`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fa929f54f211e1c98cfa837fbc26e90f55704709eb5e826a5c4f48d839a3c153`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fa929f54f211e1c98cfa837fbc26e90f55704709eb5e826a5c4f48d839a3c153`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gui/menu_spec.spl
mirror: doc/06_spec/01_unit/lib/gui/menu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gui/menu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gui/menu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gui/menu_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has 0 items' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gui/menu_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'append bumps count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gui/menu_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'append twice gives count 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
