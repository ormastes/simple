# App Menu Snapshot Specification

> Tests covering AppMenuRegistry.register (design section 6.2/6.4), app_menu_snapshot_blank (design section 6.4, shell-default menu).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# App Menu Snapshot Specification

## Scenarios

### AppMenuRegistry.register (design section 6.2/6.4)

#### registers a flat menu and reports matching item/action ranges

- registers a flat menu and reports matching item/action ranges
   - Expected: snapshot.app_id equals `1u32`
   - Expected: snapshot.menu_revision equals `1u32`
   - Expected: snapshot.item_count equals `3u32`
   - Expected: snapshot.action_count equals `3u32`
   - Expected: snapshot.root_count equals `3u32`
   - Expected: registry.label_at(item0.label_string_id) equals `File`
   - Expected: action0.action_id equals `item0.action_id`
   - Expected: action0.default_target_owner_id equals `42u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers a flat menu and reports matching item/action ranges")
var registry = AppMenuRegistry.new()
val snapshot = registry.register(1u32, 1u32, 42u32, ["File", "Edit", "View"], 42u32)
expect(snapshot.app_id).to_equal(1u32)
expect(snapshot.menu_revision).to_equal(1u32)
expect(snapshot.item_count).to_equal(3u32)
expect(snapshot.action_count).to_equal(3u32)
expect(snapshot.root_count).to_equal(3u32)

val item0 = registry.item_at(snapshot.item_start)
expect(registry.label_at(item0.label_string_id)).to_equal("File")
val action0 = registry.action_at(snapshot.action_start)
expect(action0.action_id).to_equal(item0.action_id)
expect(action0.default_target_owner_id).to_equal(42u32)
print "l8_app_menu_registry_register items={snapshot.item_count} actions={snapshot.action_count}"
```

</details>

#### finds a registered app via lookup() and returns nil for an unknown one

- finds a registered app via lookup() and returns nil for an unknown one
   - Expected: found.app_id equals `5u32`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a registered app via lookup() and returns nil for an unknown one")
var registry = AppMenuRegistry.new()
registry.register(5u32, 1u32, 7u32, ["Quit"], 7u32)
if val found = registry.lookup(5u32):
    expect(found.app_id).to_equal(5u32)
else:
    expect(true).to_equal(false)
val missing = registry.lookup(999u32)
expect(missing).to_be_nil()
```

</details>

#### bumps menu_revision on re-register and keeps the app_id stable

- bumps menu_revision on re-register and keeps the app_id stable
   - Expected: first.menu_revision equals `1u32`
   - Expected: second.menu_revision equals `2u32`
   - Expected: second.app_id equals `first.app_id`
   - Expected: second.item_count equals `3u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bumps menu_revision on re-register and keeps the app_id stable")
var registry = AppMenuRegistry.new()
val first = registry.register(2u32, 1u32, 10u32, ["A", "B"], 10u32)
val second = registry.register(2u32, 1u32, 10u32, ["A", "B", "C"], 10u32)
expect(first.menu_revision).to_equal(1u32)
expect(second.menu_revision).to_equal(2u32)
expect(second.app_id).to_equal(first.app_id)
expect(second.item_count).to_equal(3u32)
print "l8_app_menu_registry_revision first={first.menu_revision} second={second.menu_revision}"
```

</details>

### app_menu_snapshot_blank (design section 6.4, shell-default menu)

#### reports a zero-item, zero-action snapshot with NO_ID app identity

- reports a zero-item, zero-action snapshot with NO_ID app identity
   - Expected: blank.app_id equals `DRAW_IR_V3_NO_ID`
   - Expected: blank.focused_owner_id equals `DRAW_IR_V3_NO_ID`
   - Expected: blank.item_count equals `0u32`
   - Expected: blank.action_count equals `0u32`
   - Expected: blank.root_count equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a zero-item, zero-action snapshot with NO_ID app identity")
val blank = app_menu_snapshot_blank()
expect(blank.app_id).to_equal(DRAW_IR_V3_NO_ID)
expect(blank.focused_owner_id).to_equal(DRAW_IR_V3_NO_ID)
expect(blank.item_count).to_equal(0u32)
expect(blank.action_count).to_equal(0u32)
expect(blank.root_count).to_equal(0u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/app_menu_snapshot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AppMenuRegistry.register (design section 6.2/6.4), app_menu_snapshot_blank (design section 6.4, shell-default menu).
- AppMenuRegistry.register (design section 6.2/6.4)
- app_menu_snapshot_blank (design section 6.4, shell-default menu)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `b17627ca1477883bfff6ebd6a52497afcc24ffc955b0bcd8982059701a38785e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b17627ca1477883bfff6ebd6a52497afcc24ffc955b0bcd8982059701a38785e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b17627ca1477883bfff6ebd6a52497afcc24ffc955b0bcd8982059701a38785e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/app_menu_snapshot_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/app_menu_snapshot_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/app_menu_snapshot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/app_menu_snapshot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/app_menu_snapshot_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers a flat menu and reports matching item/action ranges' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/app_menu_snapshot_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds a registered app via lookup() and returns nil for an unknown one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/app_menu_snapshot_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bumps menu_revision on re-register and keeps the app_id stable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
