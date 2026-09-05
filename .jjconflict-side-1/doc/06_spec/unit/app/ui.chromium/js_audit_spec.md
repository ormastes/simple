# Js Audit Specification

> Tests covering Chromium M9 Test262Runner, Chromium M9 Test262Runner.classify, Chromium M9 js_audit_default_subset, Chromium M9 Test262Report, Chromium M9 js_audit_known_crashes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Js Audit Specification

## Scenarios

### Chromium M9 Test262Runner

#### fresh runner starts with zero totals

- fresh runner starts with zero totals


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fresh runner starts with zero totals")
val r = Test262Runner.new("interpreter")
expect(r.total() == 0).to_be_true()
expect(r.pass_rate_pct() == 0).to_be_true()
```

</details>

#### record(pass) bumps the pass bucket

- record(pass) bumps the pass bucket


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("record(pass) bumps the pass bucket")
var r = Test262Runner.new("interpreter")
r.record(OUTCOME_PASS)
expect(r.pass_count == 1).to_be_true()
expect(r.total() == 1).to_be_true()
```

</details>

#### record(fail) bumps only the fail bucket

- record(fail) bumps only the fail bucket


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("record(fail) bumps only the fail bucket")
var r = Test262Runner.new("interpreter")
r.record(OUTCOME_FAIL)
expect(r.fail_count == 1).to_be_true()
expect(r.pass_count == 0).to_be_true()
```

</details>

#### record(crash) bumps only the crash bucket

- record(crash) bumps only the crash bucket


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("record(crash) bumps only the crash bucket")
var r = Test262Runner.new("interpreter")
r.record(OUTCOME_CRASH)
expect(r.crash_count == 1).to_be_true()
```

</details>

#### record(skip) bumps only the skip bucket

- record(skip) bumps only the skip bucket


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("record(skip) bumps only the skip bucket")
var r = Test262Runner.new("interpreter")
r.record(OUTCOME_SKIP)
expect(r.skip_count == 1).to_be_true()
```

</details>

#### pass_rate_pct is 100 when every case passes

- pass_rate_pct is 100 when every case passes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pass_rate_pct is 100 when every case passes")
var r = Test262Runner.new("interpreter")
r.record(OUTCOME_PASS)
r.record(OUTCOME_PASS)
r.record(OUTCOME_PASS)
expect(r.pass_rate_pct() == 100).to_be_true()
```

</details>

#### pass_rate_pct is 50 for one pass and one fail

- pass_rate_pct is 50 for one pass and one fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pass_rate_pct is 50 for one pass and one fail")
var r = Test262Runner.new("interpreter")
r.record(OUTCOME_PASS)
r.record(OUTCOME_FAIL)
expect(r.pass_rate_pct() == 50).to_be_true()
```

</details>

### Chromium M9 Test262Runner.classify
_A negative case flips pass<->fail but leaves crash/skip alone._

#### non-negative pass stays pass

- non-negative pass stays pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-negative pass stays pass")
var r = Test262Runner.new("interpreter")
val c = Test262Case.new("x", "1", false)
expect(r.classify(c, OUTCOME_PASS) == OUTCOME_PASS).to_be_true()
```

</details>

#### non-negative fail stays fail

- non-negative fail stays fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-negative fail stays fail")
var r = Test262Runner.new("interpreter")
val c = Test262Case.new("x", "1", false)
expect(r.classify(c, OUTCOME_FAIL) == OUTCOME_FAIL).to_be_true()
```

</details>

#### negative case that threw becomes pass

- negative case that threw becomes pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negative case that threw becomes pass")
var r = Test262Runner.new("interpreter")
val c = Test262Case.new("neg", "throw 1", true)
expect(r.classify(c, OUTCOME_FAIL) == OUTCOME_PASS).to_be_true()
```

</details>

#### negative case that did not throw becomes fail

- negative case that did not throw becomes fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negative case that did not throw becomes fail")
var r = Test262Runner.new("interpreter")
val c = Test262Case.new("neg", "1", true)
expect(r.classify(c, OUTCOME_PASS) == OUTCOME_FAIL).to_be_true()
```

</details>

#### crash on a negative case is still a crash

- crash on a negative case is still a crash


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("crash on a negative case is still a crash")
var r = Test262Runner.new("interpreter")
val c = Test262Case.new("neg", "1", true)
expect(r.classify(c, OUTCOME_CRASH) == OUTCOME_CRASH).to_be_true()
```

</details>

#### skip on a negative case is still a skip

- skip on a negative case is still a skip


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skip on a negative case is still a skip")
var r = Test262Runner.new("interpreter")
val c = Test262Case.new("neg", "1", true)
expect(r.classify(c, OUTCOME_SKIP) == OUTCOME_SKIP).to_be_true()
```

</details>

#### run_case bumps the resolved bucket, not the raw one

- run_case bumps the resolved bucket, not the raw one


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("run_case bumps the resolved bucket, not the raw one")
var r = Test262Runner.new("interpreter")
val c = Test262Case.new("neg", "throw 1", true)
val resolved = r.run_case(c, OUTCOME_FAIL)
expect(resolved == OUTCOME_PASS).to_be_true()
expect(r.pass_count == 1).to_be_true()
expect(r.fail_count == 0).to_be_true()
```

</details>

### Chromium M9 js_audit_default_subset

#### has exactly five baseline cases

- has exactly five baseline cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has exactly five baseline cases")
val subset = js_audit_default_subset()
expect(subset.len() == 5).to_be_true()
```

</details>

#### contains a negative case

- contains a negative case


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains a negative case")
val subset = js_audit_default_subset()
var found = false
for c in subset:
    if c.negative:
        found = true
expect(found).to_be_true()
```

</details>

#### has at least four positive cases

- has at least four positive cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has at least four positive cases")
val subset = js_audit_default_subset()
var positives = 0
for c in subset:
    if c.negative == false:
        positives = positives + 1
expect(positives >= 4).to_be_true()
```

</details>

### Chromium M9 Test262Report
_Checked-in pass-rate snapshots — the `#2` acceptance criterion._

#### canonical interpreter snapshot is 5/0/0/0

- canonical interpreter snapshot is 5/0/0/0


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("canonical interpreter snapshot is 5/0/0/0")
val rep = Test262Report.canonical()
expect(rep.pass_count == 5).to_be_true()
expect(rep.fail_count == 0).to_be_true()
expect(rep.crash_count == 0).to_be_true()
expect(rep.skip_count == 0).to_be_true()
```

</details>

#### canonical snapshot reports 100% pass rate

- canonical snapshot reports 100% pass rate


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("canonical snapshot reports 100% pass rate")
val rep = Test262Report.canonical()
expect(rep.pass_rate_pct() == 100).to_be_true()
```

</details>

#### canonical snapshot is tagged interpreter / m9-baseline

- canonical snapshot is tagged interpreter / m9-baseline


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("canonical snapshot is tagged interpreter / m9-baseline")
val rep = Test262Report.canonical()
expect(rep.backend == "interpreter").to_be_true()
expect(rep.subset == "m9-baseline").to_be_true()
```

</details>

#### jit_today snapshot is all-skipped

- jit_today snapshot is all-skipped


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("jit_today snapshot is all-skipped")
val rep = Test262Report.jit_today()
expect(rep.skip_count == 5).to_be_true()
expect(rep.pass_count == 0).to_be_true()
```

</details>

#### jit_today snapshot reports 0% pass rate

- jit_today snapshot reports 0% pass rate


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("jit_today snapshot reports 0% pass rate")
val rep = Test262Report.jit_today()
expect(rep.pass_rate_pct() == 0).to_be_true()
```

</details>

#### full_corpus_today is the `not run yet` sentinel

- full_corpus_today is the `not run yet` sentinel


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full_corpus_today is the `not run yet` sentinel")
val rep = Test262Report.full_corpus_today()
expect(rep.total() == 0).to_be_true()
expect(rep.pass_rate_pct() == 0).to_be_true()
expect(rep.subset == "test262-full").to_be_true()
```

</details>

### Chromium M9 js_audit_known_crashes

#### is non-empty

- is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is non-empty")
val crashes = js_audit_known_crashes()
expect(crashes.len() > 0).to_be_true()
```

</details>

#### covers at least eight categories

- covers at least eight categories


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers at least eight categories")
# Anything shorter means we're hiding known gaps.
expect(js_audit_crash_count() >= 8).to_be_true()
```

</details>

#### every entry has a non-empty id

- every entry has a non-empty id


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every entry has a non-empty id")
val crashes = js_audit_known_crashes()
var ok = true
for c in crashes:
    if c.id.len() == 0:
        ok = false
expect(ok).to_be_true()
```

</details>

#### every entry has a severity tag

- every entry has a severity tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every entry has a severity tag")
val crashes = js_audit_known_crashes()
var ok = true
for c in crashes:
    val s = c.severity
    val valid = (s == "crash") || (s == "wrong-result") || (s == "unsupported")
    if valid == false:
        ok = false
expect(ok).to_be_true()
```

</details>

#### mentions the JIT backend gap

- mentions the JIT backend gap


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mentions the JIT backend gap")
val crashes = js_audit_known_crashes()
var found = false
for c in crashes:
    if c.id == "JIT_BACKEND_DISABLED":
        found = true
expect(found).to_be_true()
```

</details>

#### mentions the test262 wiring gap

- mentions the test262 wiring gap


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mentions the test262 wiring gap")
val crashes = js_audit_known_crashes()
var found = false
for c in crashes:
    if c.id == "TEST262_NOT_WIRED":
        found = true
expect(found).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui.chromium/js_audit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Chromium M9 Test262Runner, Chromium M9 Test262Runner.classify, Chromium M9 js_audit_default_subset, Chromium M9 Test262Report, Chromium M9 js_audit_known_crashes.
- Chromium M9 Test262Runner
- Chromium M9 Test262Runner.classify
- Chromium M9 js_audit_default_subset
- Chromium M9 Test262Report
- Chromium M9 js_audit_known_crashes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
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

- Canonical SPipe generation for source `084e8961f351cdd58cd3f86e0ad181c78f01c5da6e831526686a0d32bf71b543`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `084e8961f351cdd58cd3f86e0ad181c78f01c5da6e831526686a0d32bf71b543`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `084e8961f351cdd58cd3f86e0ad181c78f01c5da6e831526686a0d32bf71b543`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui.chromium/js_audit_spec.spl
mirror: doc/06_spec/unit/app/ui.chromium/js_audit_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui.chromium/js_audit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui.chromium/js_audit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui.chromium/js_audit_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fresh runner starts with zero totals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium/js_audit_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'record(pass) bumps the pass bucket' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium/js_audit_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'record(fail) bumps only the fail bucket' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
