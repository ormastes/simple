# margin_collapse_spec

> Purpose: Prove that collapse_margins_signed positive-positive.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# margin_collapse_spec

Purpose: Prove that collapse_margins_signed positive-positive.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/margin_collapse_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that collapse_margins_signed positive-positive.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### collapse_margins_signed positive-positive

#### AC-3: collapses two positive margins to the larger value

- Verify: AC-3: collapses two positive margins to the larger value
   - Expected: result equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: AC-3: collapses two positive margins to the larger value")
# @req: REQ-BROWSER-ENGINE-MARGIN-COLLAPSE-SPEC-SPL-001
val result = collapse_margins_signed(20, 10)
expect(result).to_equal(20)  # oracle: 20 — named expected value from the requirement
```

</details>

#### AC-3: collapses equal positive margins to same value

- Verify: AC-3: collapses equal positive margins to same value
   - Expected: result equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: AC-3: collapses equal positive margins to same value")
val result = collapse_margins_signed(15, 15)
expect(result).to_equal(15)  # oracle: 15 — named expected value from the requirement
```

</details>

#### AC-3: collapses zero and positive to positive

- Verify: AC-3: collapses zero and positive to positive
   - Expected: result equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: AC-3: collapses zero and positive to positive")
val result = collapse_margins_signed(0, 30)
expect(result).to_equal(30)  # oracle: 30 — named expected value from the requirement
```

</details>

### collapse_margins_signed negative-positive mixed

#### AC-3: mixed margins: max(positives) + min(negatives)

- Verify: AC-3: mixed margins: max(positives) + min(negatives)
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: AC-3: mixed margins: max(positives) + min(negatives)")
# max(10) + min(-5) = 10 + (-5) = 5
val result = collapse_margins_signed(10, -5)
expect(result).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

#### AC-3: large negative with small positive gives negative result

- Verify: AC-3: large negative with small positive gives negative result
   - Expected: result equals `-18`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: AC-3: large negative with small positive gives negative result")
# max(2) + min(-20) = 2 + (-20) = -18
val result = collapse_margins_signed(2, -20)
expect(result).to_equal(-18)  # oracle: -18 — named expected value from the requirement
```

</details>

#### AC-3: two negatives produce the most-negative value

- Verify: AC-3: two negatives produce the most-negative value
   - Expected: result equals `-12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: AC-3: two negatives produce the most-negative value")
# max(negatives only) = 0; min(-8, -12) = -12 → result = -12
val result = collapse_margins_signed(-8, -12)
expect(result).to_equal(-12)  # oracle: -12 — named expected value from the requirement
```

</details>

### collapse_margins_signed parent-child collapse

#### AC-3: parent-child top margin collapses when no border/padding

- Verify: AC-3: parent-child top margin collapses when no border/padding
   - Expected: result equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: AC-3: parent-child top margin collapses when no border/padding")
# Simulated: parent margin-top=10, child margin-top=20 → 20
val result = collapse_margins_signed(10, 20)
expect(result).to_equal(20)  # oracle: 20 — named expected value from the requirement
```

</details>

#### AC-3: parent-child bottom margin collapses symmetrically

- Verify: AC-3: parent-child bottom margin collapses symmetrically
   - Expected: result equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: AC-3: parent-child bottom margin collapses symmetrically")
val result = collapse_margins_signed(16, 8)
expect(result).to_equal(16)  # oracle: 16 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-BROWSER-ENGINE-MARGIN-COLLAPSE-SPEC-SPL-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `258e3a6568cd1deedcae56f7457dbe8819eaf596844f48f5d15e540d90ac3f91`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `258e3a6568cd1deedcae56f7457dbe8819eaf596844f48f5d15e540d90ac3f91`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `258e3a6568cd1deedcae56f7457dbe8819eaf596844f48f5d15e540d90ac3f91`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/browser_engine/margin_collapse_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/margin_collapse_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/margin_collapse_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/margin_collapse_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/margin_collapse_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/browser_engine/margin_collapse_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/01_unit/browser_engine/margin_collapse_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: collapses two positive margins to the larger value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/margin_collapse_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: collapses equal positive margins to same value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/margin_collapse_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: collapses zero and positive to positive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
