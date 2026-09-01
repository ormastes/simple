# `expect(x).to_be_true()` Inside an `it` Block

> As a spec author I need `expect(value).to_be_true()` to PASS when the value is

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `expect(x).to_be_true()` Inside an `it` Block

As a spec author I need `expect(value).to_be_true()` to PASS when the value is

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/spec_to_be_true_in_it_block_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

As a spec author I need `expect(value).to_be_true()` to PASS when the value is
genuinely true, and to FAIL when it is not. The reported defect
(doc/08_tracking/bug/spipe_to_be_true_matcher_errors_in_interpreter_itblock_2026-06-04.md)
was that the matcher errored inside an interpreter `it` block even for a
genuinely-true subject -- a false RED, which erodes trust in every matcher.

This also covers the negation path, so a matcher that silently passes
everything (a false GREEN, the worse failure) is caught too.

## Scenarios

### expect().to_be_true / to_be_false inside an it block

#### accepts a genuinely true literal

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts a genuinely true literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a genuinely true literal")
expect(true).to_be_true()
```

</details>

#### accepts a genuinely true computed expression

- accepts a genuinely true computed expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a genuinely true computed expression")
val condition = 2 + 2 == 4
expect(condition).to_be_true()
```

</details>

#### accepts to_be_false on a genuinely false expression

- accepts to_be_false on a genuinely false expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts to_be_false on a genuinely false expression")
val condition = 2 + 2 == 5
expect(condition).to_be_false()
```

</details>

#### keeps to_be_true and to_be_false distinguishable, not vacuous

- keeps to_be_true and to_be_false distinguishable, not vacuous


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps to_be_true and to_be_false distinguishable, not vacuous")
# If the matcher were a no-op, both directions would pass on the same
# subject. Assert the pair disagrees using the boolean itself.
val truth = true
expect(truth).to_be_true()
expect(not truth).to_be_false()
```

</details>

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

- Canonical SPipe generation for source `ddb016e920296714f9aaf491f93d84b5fbe2786fd3c5e60d54f5edce2d09ab68`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ddb016e920296714f9aaf491f93d84b5fbe2786fd3c5e60d54f5edce2d09ab68`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ddb016e920296714f9aaf491f93d84b5fbe2786fd3c5e60d54f5edce2d09ab68`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/std/spec_to_be_true_in_it_block_spec.spl
mirror: doc/06_spec/01_unit/std/spec_to_be_true_in_it_block_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/spec_to_be_true_in_it_block_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/spec_to_be_true_in_it_block_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/spec_to_be_true_in_it_block_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a genuinely true literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/spec_to_be_true_in_it_block_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a genuinely true computed expression' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/spec_to_be_true_in_it_block_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts to_be_false on a genuinely false expression' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
