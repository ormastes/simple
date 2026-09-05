# Defect CLASS: truncating a diagnostic BEFORE classifying it

> Class statement: when a tool derives a category from a message, any truncation

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Defect CLASS: truncating a diagnostic BEFORE classifying it

Class statement: when a tool derives a category from a message, any truncation

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/scripts/truncate_before_classify_defect_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Class statement: when a tool derives a category from a message, any truncation
must happen strictly AFTER the match. Truncate-then-match silently drops every
input whose distinguishing token sits past the cut, and — the reason it is
dangerous rather than merely untidy — it fails toward the catch-all bucket, so
the output still looks complete. The concrete instance is
`scripts/check/check-no-jit-module-drop.shs`; see
`jit_drop_guard_bucket_truncation_spec.spl`.

This spec is deliberately NOT about that one script: it models both orders over
the same inputs and asserts they diverge exactly where the class predicts,
INCLUDING a positive control (a short message) where the two orders must agree
— without that control, "they differ" would also be satisfied by a broken
classifier that always disagreed.

Run with: bin/simple test test/01_unit/scripts/truncate_before_classify_defect_class_spec.spl

## Scenarios

### truncate-then-classify loses categories; classify-then-truncate does not

#### a keyword past the cut is lost when the message is truncated first

- a keyword past the cut is lost when the message is truncated first
   - Expected: _classify(msg) equals `emit`
   - Expected: _classify_after_truncation(msg) equals `other`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a keyword past the cut is lost when the message is truncated first")
val msg = _pad("error: compile failed (", 150) + "): SMF emission failed: no code"
assert_true(msg.length() > _CUT)
expect(_classify(msg)).to_equal("emit")
expect(_classify_after_truncation(msg)).to_equal("other")
```

</details>

#### holds for every member of the family, not just one keyword

- holds for every member of the family, not just one keyword
   - Expected: _classify(a) equals `import`
   - Expected: _classify(b) equals `undefined`
   - Expected: _classify(c) equals `codegen`
   - Expected: _classify_after_truncation(a) equals `other`
   - Expected: _classify_after_truncation(b) equals `other`
   - Expected: _classify_after_truncation(c) equals `other`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("holds for every member of the family, not just one keyword")
val a = _pad("error: a (", 150) + "): cannot resolve import `mem`"
val b = _pad("error: b (", 150) + "): Undefined(\"undefined identifier: Port\")"
val c = _pad("error: c (", 150) + "): Failed to parse object into SMF"
expect(_classify(a)).to_equal("import")
expect(_classify(b)).to_equal("undefined")
expect(_classify(c)).to_equal("codegen")
expect(_classify_after_truncation(a)).to_equal("other")
expect(_classify_after_truncation(b)).to_equal("other")
expect(_classify_after_truncation(c)).to_equal("other")
```

</details>

#### POSITIVE CONTROL: a message shorter than the cut classifies identically both ways

- POSITIVE CONTROL: a message shorter than the cut classifies identically both ways
   - Expected: _classify(short) equals `emit`
   - Expected: _classify_after_truncation(short) equals `emit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("POSITIVE CONTROL: a message shorter than the cut classifies identically both ways")
# Without this, the assertions above would also pass for a classifier
# that was simply broken in all cases.
val short = "error: x: SMF emission failed"
assert_true(short.length() <= _CUT)
expect(_classify(short)).to_equal("emit")
expect(_classify_after_truncation(short)).to_equal("emit")
```

</details>

#### POSITIVE CONTROL: a genuinely uncategorised long message is `other` both ways

- POSITIVE CONTROL: a genuinely uncategorised long message is `other` both ways
   - Expected: _classify(unknown) equals `other`
   - Expected: _classify_after_truncation(unknown) equals `other`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("POSITIVE CONTROL: a genuinely uncategorised long message is `other` both ways")
val unknown = _pad("error: d (", 150) + "): some cause nobody has a bucket for"
expect(_classify(unknown)).to_equal("other")
expect(_classify_after_truncation(unknown)).to_equal("other")
```

</details>

#### truncation still bounds what gets RECORDED

- truncation still bounds what gets RECORDED
   - Expected: _truncate(msg).length() equals `_CUT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("truncation still bounds what gets RECORDED")
val msg = _pad("error: e (", 150) + "): SMF emission failed: no code"
expect(_truncate(msg).length()).to_equal(_CUT)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fc4e31e5f9f445aeb87fbcbfacbdf2cc96eb09ba67ef7c34133ad03d753b25d2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fc4e31e5f9f445aeb87fbcbfacbdf2cc96eb09ba67ef7c34133ad03d753b25d2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fc4e31e5f9f445aeb87fbcbfacbdf2cc96eb09ba67ef7c34133ad03d753b25d2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/scripts/truncate_before_classify_defect_class_spec.spl
mirror: doc/06_spec/01_unit/scripts/truncate_before_classify_defect_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/scripts/truncate_before_classify_defect_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/scripts/truncate_before_classify_defect_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/scripts/truncate_before_classify_defect_class_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a keyword past the cut is lost when the message is truncated first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/scripts/truncate_before_classify_defect_class_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'holds for every member of the family, not just one keyword' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/scripts/truncate_before_classify_defect_class_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'POSITIVE CONTROL: a message shorter than the cut classifies identically both ways' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
