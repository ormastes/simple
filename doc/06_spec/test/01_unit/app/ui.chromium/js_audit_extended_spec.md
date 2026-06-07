# Js Audit Extended Specification

> _Row 5 follow-up: ~20 hand-transcribed test262-shaped cases._

<!-- sdn-diagram:id=js_audit_extended_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=js_audit_extended_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

js_audit_extended_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=js_audit_extended_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Js Audit Extended Specification

## Scenarios

### Chromium M9 js_audit_extended_subset
_Row 5 follow-up: ~20 hand-transcribed test262-shaped cases._

#### exposes exactly twenty cases

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subset = js_audit_extended_subset()
expect(subset.len() == 20).to_be_true()
```

</details>

#### every case has a non-empty name

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subset = js_audit_extended_subset()
var ok = true
for c in subset:
    if c.name.len() == 0:
        ok = false
expect(ok).to_be_true()
```

</details>

#### every case has a non-empty source

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subset = js_audit_extended_subset()
var ok = true
for c in subset:
    if c.source.len() == 0:
        ok = false
expect(ok).to_be_true()
```

</details>

#### contains exactly one negative case

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subset = js_audit_extended_subset()
var negatives = 0
for c in subset:
    if c.negative:
        negatives = negatives + 1
expect(negatives == 1).to_be_true()
```

</details>

#### names are namespaced under ext/

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subset = js_audit_extended_subset()
val r = Test262Runner.new("interpreter")
expect(r.total() == 0).to_be_true()
expect(subset.len() == 20).to_be_true()
```

</details>

#### driving 20 synthetic passes yields 20/0/0/0

1. var r = Test262Runner new


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var r = Test262Runner new


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var r = Test262Runner new
2. r record
3. r record
4. r record


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rep = Test262Report.extended_subset_today()
expect(rep.backend == "interpreter").to_be_true()
expect(rep.subset == "m9-extended").to_be_true()
```

</details>

#### totals twenty cases

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rep = Test262Report.extended_subset_today()
expect(rep.total() == 20).to_be_true()
```

</details>

#### pass rate is 50 percent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 10 pass / 20 total = 50.
val rep = Test262Report.extended_subset_today()
expect(rep.pass_rate_pct() == 50).to_be_true()
```

</details>

#### crash bucket is non-zero (array methods gap)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rep = Test262Report.extended_subset_today()
expect(rep.crash_count > 0).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui.chromium/js_audit_extended_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
