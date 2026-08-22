# @manual: primary

> Purpose: Prove that UI Dynamic Structure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that UI Dynamic Structure.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that UI Dynamic Structure.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-FEATURE-UI-DYNAMIC-001
doc/01_research/feature/REQ-FEATURE-UI-DYNAMIC-001.md
doc/03_plan/feature/REQ-FEATURE-UI-DYNAMIC-001.md
doc/04_architecture/feature/REQ-FEATURE-UI-DYNAMIC-001.md
doc/05_design/feature/REQ-FEATURE-UI-DYNAMIC-001.md

## Scenarios

### UI Dynamic Structure

#### when conditionally rendering

#### replaces a panel record with a hidden variant on upsert

- Upsert a visible panel then a hidden variant and read it back


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-UI-DYNAMIC-001
step("Upsert a visible panel then a hidden variant and read it back")
upsert_widget_record(default_widget_record("panel", "box"))
var hidden_record = default_widget_record("panel", "box")
hidden_record.visible = false
upsert_widget_record(hidden_record)
match get_widget_record("panel"):
    case None: fail("record missing")
    case Some(rec): assert_equal(rec.visible, false)
```

</details>

#### when rendering lists

#### appends keyed list items to a parent without duplicates

- Register the same child twice and count its slots


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-UI-DYNAMIC-001
step("Register the same child twice and count its slots")
register_widget_child("list", "item-0")
register_widget_child("list", "item-0")
assert_equal(get_widget_child_ids("list").len(), 1)
register_widget_child("list", "item-2")
assert_equal(get_widget_child_ids("list").contains("item-2"), true)
```

</details>

#### keeps keyed list items in registration order

- Read back the parent child list and check its order


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-UI-DYNAMIC-001
step("Read back the parent child list and check its order")
val ids = get_widget_child_ids("list")
assert_equal(ids.len(), 2)
assert_equal(ids[0], "item-0")
assert_equal(ids[1], "item-2")
```

</details>

#### when replacing structure

#### emits a ReplaceNode patch when the root identity changes

- Diff trees with different root ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-UI-DYNAMIC-001
step("Diff trees with different root ids")
upsert_widget_record(default_widget_record("root-a", "box"))
upsert_widget_record(default_widget_record("root-b", "box"))
val ui = ReactiveUI.new()
assert_equal(ui.update(WidgetNode(id: "root-a")).len(), 0)
val patches = ui.update(WidgetNode(id: "root-b"))
assert_equal(patches.len(), 1)
assert_true(patches[0].kind == PatchKind.ReplaceNode)
```

</details>

#### returns an empty patch list for an identical re-render

- Re-diff an unchanged tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-UI-DYNAMIC-001
step("Re-diff an unchanged tree")
val ui = ReactiveUI.new()
assert_equal(ui.update(WidgetNode(id: "root-a")).len(), 0)
assert_equal(ui.update(WidgetNode(id: "root-a")).len(), 0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4b91f1858e224c3800d086ca6c57eefaa75d359c7212a49b0f86a06f7beb7ec1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4b91f1858e224c3800d086ca6c57eefaa75d359c7212a49b0f86a06f7beb7ec1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4b91f1858e224c3800d086ca6c57eefaa75d359c7212a49b0f86a06f7beb7ec1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl
mirror: doc/06_spec/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replaces a panel record with a hidden variant on upsert' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'appends keyed list items to a parent without duplicates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps keyed list items in registration order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
