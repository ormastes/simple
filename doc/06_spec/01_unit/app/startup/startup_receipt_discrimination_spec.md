# Startup Receipt Discrimination Specification

> Tests covering startup receipt discriminates between startup paths.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Startup Receipt Discrimination Specification

## Scenarios

### startup receipt discriminates between startup paths

#### positive control: the same startup path yields byte-identical receipts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- positive control: the same startup path yields byte-identical receipts


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("positive control: the same startup path yields byte-identical receipts")
val a = receipt_for("script", "app/main.spl", ["x"], true)
val b = receipt_for("script", "app/main.spl", ["x"], true)
assert_eq(render_startup_receipt_sdn(a), render_startup_receipt_sdn(b))
assert_true(render_startup_receipt_sdn(a).len() > 0)
```

</details>

#### script vs native startup produce different receipts

- script vs native startup produce different receipts


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("script vs native startup produce different receipts")
val s = receipt_for("script", "app/main.spl", [], true)
val n = receipt_for("native", "bin/app", [], true)
assert_false(s.entry_kind == n.entry_kind)
assert_false(render_startup_receipt_sdn(s) == render_startup_receipt_sdn(n))
```

</details>

#### same artifact, different host mmap support, differ in load facts

- same artifact, different host mmap support, differ in load facts


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("same artifact, different host mmap support, differ in load facts")
val with_mmap = receipt_for("smf", "app/main.smf", [], true)
val without = receipt_for("smf", "app/main.smf", [], false)
assert_false(render_startup_receipt_sdn(with_mmap) == render_startup_receipt_sdn(without))
```

</details>

#### same path, different program args, differ in recorded arg count

- same path, different program args, differ in recorded arg count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("same path, different program args, differ in recorded arg count")
val one = receipt_for("script", "app/main.spl", ["a"], true)
val three = receipt_for("script", "app/main.spl", ["a", "b", "c"], true)
assert_eq(one.program_args_count, 2)  # argv0 (entry path) + "a"
assert_eq(three.program_args_count, 4)
assert_false(render_startup_receipt_sdn(one) == render_startup_receipt_sdn(three))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/startup/startup_receipt_discrimination_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering startup receipt discriminates between startup paths.
- startup receipt discriminates between startup paths

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

- Canonical SPipe generation for source `d80b26d574f5e25228bd58df547f0a15e72f004b1394e6b60c4605625a758551`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d80b26d574f5e25228bd58df547f0a15e72f004b1394e6b60c4605625a758551`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d80b26d574f5e25228bd58df547f0a15e72f004b1394e6b60c4605625a758551`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/startup/startup_receipt_discrimination_spec.spl
mirror: doc/06_spec/01_unit/app/startup/startup_receipt_discrimination_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/startup/startup_receipt_discrimination_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/startup/startup_receipt_discrimination_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/startup/startup_receipt_discrimination_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'positive control: the same startup path yields byte-identical receipts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/startup_receipt_discrimination_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'script vs native startup produce different receipts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/startup_receipt_discrimination_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'same artifact, different host mmap support, differ in load facts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
