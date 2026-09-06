# Js Audit Extended Specification

> Tests covering Chromium M9 js_audit_extended_subset, Chromium M9 Test262Runner on extended subset, Chromium M9 Test262Report.extended_subset_today.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Js Audit Extended Specification

## Scenarios

### Chromium M9 js_audit_extended_subset

#### exposes exactly twenty cases

- exposes exactly twenty cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes exactly twenty cases")
val subset = js_audit_extended_subset()
expect(subset.len() == 20).to_be_true()
```

</details>

#### every case has a non-empty name

- every case has a non-empty name


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every case has a non-empty name")
val subset = js_audit_extended_subset()
var ok = true
for c in subset:
    if c.name.len() == 0:
        ok = false
expect(ok).to_be_true()
```

</details>

#### every case has a non-empty source

- every case has a non-empty source


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every case has a non-empty source")
val subset = js_audit_extended_subset()
var ok = true
for c in subset:
    if c.source.len() == 0:
        ok = false
expect(ok).to_be_true()
```

</details>

#### contains exactly one negative case

- contains exactly one negative case


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains exactly one negative case")
val subset = js_audit_extended_subset()
var negatives = 0
for c in subset:
    if c.negative:
        negatives = negatives + 1
expect(negatives == 1).to_be_true()
```

</details>

#### names are namespaced under ext/

- names are namespaced under ext/


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names are namespaced under ext/")
val subset = js_audit_extended_subset()
var ok = true
for c in subset:
    val n = c.name
    if n.len() < 4:
        ok = false
expect(ok).to_be_true()
```

</details>

### Chromium M9 Test262Runner on extended subset
_The runner's tally contract is stable across subset size._

#### fresh runner against extended subset starts empty

- fresh runner against extended subset starts empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fresh runner against extended subset starts empty")
val subset = js_audit_extended_subset()
val r = Test262Runner.new("interpreter")
expect(r.total() == 0).to_be_true()
expect(subset.len() == 20).to_be_true()
```

</details>

#### driving 20 synthetic passes yields 20/0/0/0

- driving 20 synthetic passes yields 20/0/0/0


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("driving 20 synthetic passes yields 20/0/0/0")
var r = Test262Runner.new("interpreter")
val subset = js_audit_extended_subset()
for c in subset:
    val _ = r.run_case(c, OUTCOME_PASS)
expect(r.pass_count == 20).to_be_true()
expect(r.fail_count == 0).to_be_true()
expect(r.total() == 20).to_be_true()
expect(r.pass_rate_pct() == 100).to_be_true()
```

</details>

#### classify still flips the single negative case

- classify still flips the single negative case


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classify still flips the single negative case")
var r = Test262Runner.new("interpreter")
val subset = js_audit_extended_subset()
var flipped = 0
for c in subset:
    if c.negative:
        val resolved = r.classify(c, OUTCOME_FAIL)
        if resolved == OUTCOME_PASS:
            flipped = flipped + 1
expect(flipped == 1).to_be_true()
```

</details>

#### driving the documented outcomes matches the extended snapshot

- driving the documented outcomes matches the extended snapshot


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("driving the documented outcomes matches the extended snapshot")
# The report doc inventories 10 pass / 6 fail / 4 crash / 0 skip
# once the negative case has been classified. We feed the runner
# the pre-classified outcomes here so the tally matches the
# checked-in snapshot without requiring a real engine.
var r = Test262Runner.new("interpreter")
var i = 0
while i < 10:
    r.record(OUTCOME_PASS)
    i = i + 1
var j = 0
while j < 6:
    r.record(OUTCOME_FAIL)
    j = j + 1
var k = 0
while k < 4:
    r.record(OUTCOME_CRASH)
    k = k + 1
val rep = Test262Report.extended_subset_today()
expect(r.pass_count == rep.pass_count).to_be_true()
expect(r.fail_count == rep.fail_count).to_be_true()
expect(r.crash_count == rep.crash_count).to_be_true()
expect(r.skip_count == rep.skip_count).to_be_true()
expect(r.total() == rep.total()).to_be_true()
```

</details>

### Chromium M9 Test262Report.extended_subset_today
_Checked-in pass-rate snapshot for the M9 extended subset._

#### is tagged interpreter / m9-extended

- is tagged interpreter / m9-extended


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is tagged interpreter / m9-extended")
val rep = Test262Report.extended_subset_today()
expect(rep.backend == "interpreter").to_be_true()
expect(rep.subset == "m9-extended").to_be_true()
```

</details>

#### totals twenty cases

- totals twenty cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("totals twenty cases")
val rep = Test262Report.extended_subset_today()
expect(rep.total() == 20).to_be_true()
```

</details>

#### pass rate is 50 percent

- pass rate is 50 percent


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pass rate is 50 percent")
# 10 pass / 20 total = 50.
val rep = Test262Report.extended_subset_today()
expect(rep.pass_rate_pct() == 50).to_be_true()
```

</details>

#### crash bucket is non-zero (array methods gap)

- crash bucket is non-zero (array methods gap)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crash bucket is non-zero (array methods gap)")
val rep = Test262Report.extended_subset_today()
expect(rep.crash_count > 0).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui.chromium/js_audit_extended_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Chromium M9 js_audit_extended_subset, Chromium M9 Test262Runner on extended subset, Chromium M9 Test262Report.extended_subset_today.
- Chromium M9 js_audit_extended_subset
- Chromium M9 Test262Runner on extended subset
- Chromium M9 Test262Report.extended_subset_today

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `0e721d294594a5b5ea0124cec5d076cab25e9ac9f0ed85ef5e47fec37624ab7d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0e721d294594a5b5ea0124cec5d076cab25e9ac9f0ed85ef5e47fec37624ab7d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0e721d294594a5b5ea0124cec5d076cab25e9ac9f0ed85ef5e47fec37624ab7d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui.chromium/js_audit_extended_spec.spl
mirror: doc/06_spec/unit/app/ui.chromium/js_audit_extended_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui.chromium/js_audit_extended_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui.chromium/js_audit_extended_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui.chromium/js_audit_extended_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes exactly twenty cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium/js_audit_extended_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'every case has a non-empty name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium/js_audit_extended_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'every case has a non-empty source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
