# Drawer Model Specification

> Tests covering drawer model.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Drawer Model Specification

## Scenarios

### drawer model

#### contains primary GUI applications

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- contains primary GUI applications
   - Expected: drawer_visible_items(model)[0].name equals `Terminal`
   - Expected: drawer_visible_items(model).len() >= 8 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains primary GUI applications")
val model = primary_drawer_model()

expect(drawer_visible_items(model)[0].name).to_equal("Terminal")
expect(drawer_visible_items(model).len() >= 8).to_equal(true)
```

</details>

#### filters by app name

- filters by app name
   - Expected: visible.len() equals `1`
   - Expected: visible[0].launch_path equals `/sys/apps/editor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters by app name")
val model = drawer_set_query(primary_drawer_model(), "markdown")
val visible = drawer_visible_items(model)

expect(visible.len()).to_equal(1)
expect(visible[0].launch_path).to_equal("/sys/apps/editor")
```

</details>

#### filters by category

- filters by category
   - Expected: visible[0].name equals `Minesweeper`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters by category")
val model = drawer_set_query(primary_drawer_model(), "games")
val visible = drawer_visible_items(model)

expect(visible[0].name).to_equal("Minesweeper")
```

</details>

#### selects a launch path

- selects a launch path
   - Expected: drawer_selected_launch_path(model) equals `/sys/apps/shell`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects a launch path")
val model = drawer_select_next(primary_drawer_model())

expect(drawer_selected_launch_path(model)).to_equal("/sys/apps/shell")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/tools/desktop/drawer_model_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering drawer model.
- drawer model

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

- Canonical SPipe generation for source `40499c3657f38adf47484ae932de5412cfc5fac8d3dda93e9efdf21349437435`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `40499c3657f38adf47484ae932de5412cfc5fac8d3dda93e9efdf21349437435`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `40499c3657f38adf47484ae932de5412cfc5fac8d3dda93e9efdf21349437435`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/tools/desktop/drawer_model_spec.spl
mirror: doc/06_spec/unit/tools/desktop/drawer_model_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/tools/desktop/drawer_model_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/tools/desktop/drawer_model_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/tools/desktop/drawer_model_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/tools/desktop/drawer_model_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains primary GUI applications' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/desktop/drawer_model_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters by app name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/desktop/drawer_model_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters by category' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
