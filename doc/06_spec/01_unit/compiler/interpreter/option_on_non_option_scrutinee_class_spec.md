# Option On Non Option Scrutinee Class Specification

> Tests covering Option-shaped operations on a non-Option scrutinee.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Option On Non Option Scrutinee Class Specification

## Scenarios

### Option-shaped operations on a non-Option scrutinee

#### rejects unwrap_or on a bare i64 receiver on both engines

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects unwrap_or on a bare i64 receiver on both engines


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unwrap_or on a bare i64 receiver on both engines")
# MEASURED 2026-08-17 (live defect): jit -> "uo=<value:0x6>",
# interpreter -> "uo=6". Neither is an error.
expect(run_probe("jit", "unwrap_or_on_i64.spl")).to_not_contain("uo=")
expect(run_probe("interpreter", "unwrap_or_on_i64.spl")).to_not_contain("uo=")
```

</details>

#### rejects a Some(_) match arm against a bare i64 scrutinee on both engines

- rejects a Some(_) match arm against a bare i64 scrutinee on both engines


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a Some(_) match arm against a bare i64 scrutinee on both engines")
# MEASURED: jit -> "some=<value:0x6>", interpreter -> "some=6".
expect(run_probe("jit", "match_some_on_i64.spl")).to_not_contain("some=")
expect(run_probe("interpreter", "match_some_on_i64.spl")).to_not_contain("some=")
```

</details>

#### rejects an if-val Some() binding against a bare i64 on both engines

- rejects an if-val Some() binding against a bare i64 on both engines


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an if-val Some() binding against a bare i64 on both engines")
# MEASURED: jit -> "bound=<value:0x6>", interpreter -> "bound=6".
expect(run_probe("jit", "if_val_some_on_i64.spl")).to_not_contain("bound=")
expect(run_probe("interpreter", "if_val_some_on_i64.spl")).to_not_contain("bound=")
```

</details>

#### still accepts a GENUINE Option and returns the payload on both engines

- still accepts a GENUINE Option and returns the payload on both engines


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still accepts a GENUINE Option and returns the payload on both engines")
# Guard against a fix that outlaws Option operations wholesale. This is
# also a live independent defect: on the JIT `val o: i64? = 42` leaves the
# scalar unboxed, so unwrap_or re-reads it under TAG_FLOAT and prints a
# denormal instead of 42 (see the row doc's section 25).
expect(run_probe("interpreter", "control_real_option.spl")).to_contain("ok=42")
expect(run_probe("jit", "control_real_option.spl")).to_contain("ok=42")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/option_on_non_option_scrutinee_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Option-shaped operations on a non-Option scrutinee.
- Option-shaped operations on a non-Option scrutinee

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

- Canonical SPipe generation for source `61f6b197caf9812fcfa9eb96a58aa24b8c682abcef43012aa6c9df2640914c2b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `61f6b197caf9812fcfa9eb96a58aa24b8c682abcef43012aa6c9df2640914c2b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `61f6b197caf9812fcfa9eb96a58aa24b8c682abcef43012aa6c9df2640914c2b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/interpreter/option_on_non_option_scrutinee_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/option_on_non_option_scrutinee_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/option_on_non_option_scrutinee_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/option_on_non_option_scrutinee_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/option_on_non_option_scrutinee_class_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unwrap_or on a bare i64 receiver on both engines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/option_on_non_option_scrutinee_class_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a Some(_) match arm against a bare i64 scrutinee on both engines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/option_on_non_option_scrutinee_class_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an if-val Some() binding against a bare i64 on both engines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
