# Web Layout Manager Specification

> Tests covering web layout invalidation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Layout Manager Specification

## Scenarios

### web layout invalidation

#### classifies style fingerprints strongest first

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- classifies style fingerprints strongest first


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies style fingerprints strongest first")
val base = style_fingerprint("i", "p", "c", "m", "l", "s", "f")
expect_style_difference(base, base, StyleDifference.NoChange)
expect_style_difference(base, style_fingerprint("I", "p", "c", "m", "l", "s", "f"), StyleDifference.InheritedOnly)
expect_style_difference(base, style_fingerprint("i", "P", "c", "m", "l", "s", "f"), StyleDifference.PaintOnly)
expect_style_difference(base, style_fingerprint("i", "p", "C", "m", "l", "s", "f"), StyleDifference.CompositeOnly)
expect_style_difference(base, style_fingerprint("i", "p", "c", "M", "l", "s", "f"), StyleDifference.IntrinsicMeasure)
expect_style_difference(base, style_fingerprint("i", "p", "c", "m", "L", "s", "f"), StyleDifference.LayoutSelf)
expect_style_difference(base, style_fingerprint("i", "p", "c", "m", "l", "S", "f"), StyleDifference.LayoutSubtree)
expect_style_difference(base, style_fingerprint("i", "p", "c", "m", "l", "s", "F"), StyleDifference.RebuildFormattingContext)
```

</details>

#### admits every supported browser profile explicitly

- admits every supported browser profile explicitly
   - Expected: web_layout_admit_profile("div", "block", false, false, false, false).profile_id equals `block`
   - Expected: web_layout_admit_profile("span", "inline", false, false, false, false).profile_id equals `inline`
   - Expected: web_layout_admit_profile("#text", "block", false, false, false, false).profile_id equals `inline`
   - Expected: web_layout_admit_profile("div", "flex", false, false, false, false).profile_id equals `flex`
   - Expected: web_layout_admit_profile("div", "grid", false, false, false, false).profile_id equals `grid`
   - Expected: web_layout_admit_profile("td", "table-cell", false, false, false, false).profile_id equals `table`
   - Expected: web_layout_admit_profile("div", "block", true, false, false, false).profile_id equals `absolute-sticky`
   - Expected: web_layout_admit_profile("div", "block", false, false, true, false).profile_id equals `scroll`
   - Expected: web_layout_admit_profile("img", "block", false, false, false, false).profile_id equals `replaced`
   - Expected: web_layout_admit_profile("img", "block", true, false, false, false).supported is false
   - Expected: web_layout_admit_profile("div", "mystery", false, false, false, false).supported is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits every supported browser profile explicitly")
expect(web_layout_admit_profile("div", "block", false, false, false, false).profile_id).to_equal("block")
expect(web_layout_admit_profile("span", "inline", false, false, false, false).profile_id).to_equal("inline")
expect(web_layout_admit_profile("#text", "block", false, false, false, false).profile_id).to_equal("inline")
expect(web_layout_admit_profile("div", "flex", false, false, false, false).profile_id).to_equal("flex")
expect(web_layout_admit_profile("div", "grid", false, false, false, false).profile_id).to_equal("grid")
expect(web_layout_admit_profile("td", "table-cell", false, false, false, false).profile_id).to_equal("table")
expect(web_layout_admit_profile("div", "block", true, false, false, false).profile_id).to_equal("absolute-sticky")
expect(web_layout_admit_profile("div", "block", false, false, true, false).profile_id).to_equal("scroll")
expect(web_layout_admit_profile("img", "block", false, false, false, false).profile_id).to_equal("replaced")
expect(web_layout_admit_profile("img", "block", true, false, false, false).supported).to_equal(false)
expect(web_layout_admit_profile("div", "mystery", false, false, false, false).supported).to_equal(false)
```

</details>

#### keeps no-layout changes out of the frontier

- keeps no-layout changes out of the frontier
   - Expected: frontier.invalidated_ids equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps no-layout changes out of the frontier")
val frontier = web_layout_dirty_frontier([
    change(WebLayoutMutationKind.StyleMutation, StyleDifference.PaintOnly, 1, 1, [], [], [], [], [], [], []),
    change(WebLayoutMutationKind.StyleMutation, StyleDifference.CompositeOnly, 2, 1, [], [], [], [], [], [], [])
])
expect(frontier.invalidated_ids).to_equal([])
```

</details>

#### merges mixed changes per id in stable order

- merges mixed changes per id in stable order
   - Expected: frontier.invalidated_ids equals `[2, 1, 3, 4, 5, 6]`
   - Expected: frontier.dirty_nodes[5].dirty_bits equals `DIRTY_LAYOUT | DIRTY_HIT_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("merges mixed changes per id in stable order")
val frontier = web_layout_dirty_frontier([
    change(WebLayoutMutationKind.StyleMutation, StyleDifference.IntrinsicMeasure, 2, 1, [], [], [3], [1], [], [], []),
    change(WebLayoutMutationKind.Insert, StyleDifference.NoChange, 0, 1, [5], [], [], [], [4], [], []),
    change(WebLayoutMutationKind.FontResource, StyleDifference.NoChange, 0, 0, [], [], [3], [1], [], [2], []),
    change(WebLayoutMutationKind.Viewport, StyleDifference.NoChange, 0, 0, [], [], [], [], [], [], [6])
])
expect(frontier.invalidated_ids).to_equal([2, 1, 3, 4, 5, 6])
expect(frontier.dirty_nodes[0].dirty_bits).to_equal(
    DIRTY_RESOURCE | DIRTY_INTRINSIC_MEASURE | DIRTY_LAYOUT | DIRTY_HIT_TEST
)
expect(frontier.dirty_nodes[1].dirty_bits).to_equal(
    DIRTY_INTRINSIC_MEASURE | DIRTY_LAYOUT | DIRTY_HIT_TEST
)
expect(frontier.dirty_nodes[5].dirty_bits).to_equal(DIRTY_LAYOUT | DIRTY_HIT_TEST)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu_web/layout/web_layout_manager_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering web layout invalidation.
- web layout invalidation

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

- Canonical SPipe generation for source `48f300e57542226b08ffb48cf52ae3ce586b6eb90ba066e4b7a1efd59bac664a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `48f300e57542226b08ffb48cf52ae3ce586b6eb90ba066e4b7a1efd59bac664a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `48f300e57542226b08ffb48cf52ae3ce586b6eb90ba066e4b7a1efd59bac664a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gpu_web/layout/web_layout_manager_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu_web/layout/web_layout_manager_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu_web/layout/web_layout_manager_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu_web/layout/web_layout_manager_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu_web/layout/web_layout_manager_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies style fingerprints strongest first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu_web/layout/web_layout_manager_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits every supported browser profile explicitly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu_web/layout/web_layout_manager_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps no-layout changes out of the frontier' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
