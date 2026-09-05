# Js Audit Specification

> _Pure tally logic for the JS audit runner._

<!-- sdn-diagram:id=js_audit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=js_audit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

js_audit_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=js_audit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Js Audit Specification

## Scenarios

### Chromium M9 Test262Runner
_Pure tally logic for the JS audit runner._

#### fresh runner starts with zero totals

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Test262Runner.new("interpreter")
expect(r.total() == 0).to_be_true()
expect(r.pass_rate_pct() == 0).to_be_true()
```

</details>

#### record(pass) bumps the pass bucket

1. var r = Test262Runner new
2. r record


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Test262Runner.new("interpreter")
r.record(OUTCOME_PASS)
expect(r.pass_count == 1).to_be_true()
expect(r.total() == 1).to_be_true()
```

</details>

#### record(fail) bumps only the fail bucket

1. var r = Test262Runner new
2. r record


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Test262Runner.new("interpreter")
r.record(OUTCOME_FAIL)
expect(r.fail_count == 1).to_be_true()
expect(r.pass_count == 0).to_be_true()
```

</details>

#### record(crash) bumps only the crash bucket

1. var r = Test262Runner new
2. r record


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Test262Runner.new("interpreter")
r.record(OUTCOME_CRASH)
expect(r.crash_count == 1).to_be_true()
```

</details>

#### record(skip) bumps only the skip bucket

1. var r = Test262Runner new
2. r record


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Test262Runner.new("interpreter")
r.record(OUTCOME_SKIP)
expect(r.skip_count == 1).to_be_true()
```

</details>

#### pass_rate_pct is 100 when every case passes

1. var r = Test262Runner new
2. r record
3. r record
4. r record


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Test262Runner.new("interpreter")
r.record(OUTCOME_PASS)
r.record(OUTCOME_PASS)
r.record(OUTCOME_PASS)
expect(r.pass_rate_pct() == 100).to_be_true()
```

</details>

#### pass_rate_pct is 50 for one pass and one fail

1. var r = Test262Runner new
2. r record
3. r record


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Test262Runner.new("interpreter")
r.record(OUTCOME_PASS)
r.record(OUTCOME_FAIL)
expect(r.pass_rate_pct() == 50).to_be_true()
```

</details>

### Chromium M9 Test262Runner.classify
_A negative case flips pass<->fail but leaves crash/skip alone._

#### non-negative pass stays pass

1. var r = Test262Runner new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Test262Runner.new("interpreter")
val c = Test262Case.new("x", "1", false)
expect(r.classify(c, OUTCOME_PASS) == OUTCOME_PASS).to_be_true()
```

</details>

#### non-negative fail stays fail

1. var r = Test262Runner new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Test262Runner.new("interpreter")
val c = Test262Case.new("x", "1", false)
expect(r.classify(c, OUTCOME_FAIL) == OUTCOME_FAIL).to_be_true()
```

</details>

#### negative case that threw becomes pass

1. var r = Test262Runner new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Test262Runner.new("interpreter")
val c = Test262Case.new("neg", "throw 1", true)
expect(r.classify(c, OUTCOME_FAIL) == OUTCOME_PASS).to_be_true()
```

</details>

#### negative case that did not throw becomes fail

1. var r = Test262Runner new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Test262Runner.new("interpreter")
val c = Test262Case.new("neg", "1", true)
expect(r.classify(c, OUTCOME_PASS) == OUTCOME_FAIL).to_be_true()
```

</details>

#### crash on a negative case is still a crash

1. var r = Test262Runner new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Test262Runner.new("interpreter")
val c = Test262Case.new("neg", "1", true)
expect(r.classify(c, OUTCOME_CRASH) == OUTCOME_CRASH).to_be_true()
```

</details>

#### skip on a negative case is still a skip

1. var r = Test262Runner new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Test262Runner.new("interpreter")
val c = Test262Case.new("neg", "1", true)
expect(r.classify(c, OUTCOME_SKIP) == OUTCOME_SKIP).to_be_true()
```

</details>

#### run_case bumps the resolved bucket, not the raw one

1. var r = Test262Runner new


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subset = js_audit_default_subset()
expect(subset.len() == 5).to_be_true()
```

</details>

#### contains a negative case

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subset = js_audit_default_subset()
var found = false
for c in subset:
    if c.negative:
        found = true
expect(found).to_be_true()
```

</details>

#### has at least four positive cases

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subset = js_audit_default_subset()
var positives = 0
for c in subset:
    if c.negative == false:
        positives = positives + 1
expect(positives >= 4).to_be_true()
```

</details>

### Chromium M9 Test262Report
_Checked-in pass-rate snapshots — the `#2` acceptance criterion.""_

#### canonical interpreter snapshot is 5/0/0/0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rep = Test262Report.canonical()
expect(rep.pass_count == 5).to_be_true()
expect(rep.fail_count == 0).to_be_true()
expect(rep.crash_count == 0).to_be_true()
expect(rep.skip_count == 0).to_be_true()
```

</details>

#### canonical snapshot reports 100% pass rate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rep = Test262Report.canonical()
expect(rep.pass_rate_pct() == 100).to_be_true()
```

</details>

#### canonical snapshot is tagged interpreter / m9-baseline

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rep = Test262Report.canonical()
expect(rep.backend == "interpreter").to_be_true()
expect(rep.subset == "m9-baseline").to_be_true()
```

</details>

#### jit_today snapshot is all-skipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rep = Test262Report.jit_today()
expect(rep.skip_count == 5).to_be_true()
expect(rep.pass_count == 0).to_be_true()
```

</details>

#### jit_today snapshot reports 0% pass rate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rep = Test262Report.jit_today()
expect(rep.pass_rate_pct() == 0).to_be_true()
```

</details>

#### full_corpus_today is the `not run yet` sentinel

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rep = Test262Report.full_corpus_today()
expect(rep.total() == 0).to_be_true()
expect(rep.pass_rate_pct() == 0).to_be_true()
expect(rep.subset == "test262-full").to_be_true()
```

</details>

### Chromium M9 js_audit_known_crashes

#### is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val crashes = js_audit_known_crashes()
expect(crashes.len() > 0).to_be_true()
```

</details>

#### covers at least eight categories

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Anything shorter means we're hiding known gaps.
expect(js_audit_crash_count() >= 8).to_be_true()
```

</details>

#### every entry has a non-empty id

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val crashes = js_audit_known_crashes()
var ok = true
for c in crashes:
    if c.id.len() == 0:
        ok = false
expect(ok).to_be_true()
```

</details>

#### every entry has a severity tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val crashes = js_audit_known_crashes()
var found = false
for c in crashes:
    if c.id == "JIT_BACKEND_DISABLED":
        found = true
expect(found).to_be_true()
```

</details>

#### mentions the test262 wiring gap

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/ui.chromium/js_audit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
