# @manual: primary

> Purpose: Prove that UI Structural Patchset.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that UI Structural Patchset.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Runtime |
| Difficulty | 4/5 |
| Status | Planned |
| Source | `test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that UI Structural Patchset.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-FEATURE-UI-STRUCTURAL-001
doc/01_research/feature/REQ-FEATURE-UI-STRUCTURAL-001.md
doc/03_plan/feature/REQ-FEATURE-UI-STRUCTURAL-001.md
doc/04_architecture/feature/REQ-FEATURE-UI-STRUCTURAL-001.md
doc/05_design/feature/REQ-FEATURE-UI-STRUCTURAL-001.md

## Scenarios

### UI Structural Patchset

#### when computing diffs

#### detects element replacement when the node identity changes

- Diff two trees whose node ids differ


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-UI-STRUCTURAL-001
step("Diff two trees whose node ids differ")
upsert_widget_record(default_widget_record("card-a", "panel"))
upsert_widget_record(default_widget_record("card-b", "panel"))
val ui = ReactiveUI.new()
assert_equal(ui.update(WidgetNode(id: "card-a")).len(), 0)
val patches = ui.update(WidgetNode(id: "card-b"))
assert_equal(patches.len(), 1)
assert_true(patches[0].kind == PatchKind.ReplaceNode)
assert_equal(patches[0].target_id, "card-b")
assert_equal(patches[0].parent_id, "card-a")
```

</details>

#### emits no patch for an unchanged tree

- Re-diff an identical tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-UI-STRUCTURAL-001
step("Re-diff an identical tree")
val ui = ReactiveUI.new()
assert_equal(ui.update(WidgetNode(id: "card-a")).len(), 0)
assert_equal(ui.update(WidgetNode(id: "card-a")).len(), 0)
```

</details>

#### keeps a structural child registry keyed by parent

- Register children under a parent and read the order back


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-UI-STRUCTURAL-001
step("Register children under a parent and read the order back")
upsert_widget_record(default_widget_record("row", "hbox"))
register_widget_child("row", "cell-0")
register_widget_child("row", "cell-1")
val ids = get_widget_child_ids("row")
assert_equal(ids.len(), 2)
assert_equal(ids[0] + "," + ids[1], "cell-0,cell-1")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5b2ef582d4d0f4c1fc61cbe63f03b355b69405a65424add83b82e4814622d559`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5b2ef582d4d0f4c1fc61cbe63f03b355b69405a65424add83b82e4814622d559`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5b2ef582d4d0f4c1fc61cbe63f03b355b69405a65424add83b82e4814622d559`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl
mirror: doc/06_spec/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects element replacement when the node identity changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits no patch for an unchanged tree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a structural child registry keyed by parent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
