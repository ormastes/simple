# Performance & Stress Test

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Performance & Stress Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PERFORMANCE |
| Category | Performance Testing |
| Status | Implemented |
| Source | `test/05_perf/stress/file_stress_large_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Performance Test

<details>
<summary>Advanced: stress test 1</summary>

#### stress test 1 _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- stress test 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("stress test 1")
var arr = []
for i in 0..100:
    arr = arr.append(i)
check(arr.len() == 100)
```

</details>


</details>

<details>
<summary>Advanced: stress test 2</summary>

#### stress test 2 _(slow)_

- stress test 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("stress test 2")
var sum = 0
for i in 0..1000:
    sum = sum + i
check(sum == 499500)
```

</details>


</details>

<details>
<summary>Advanced: stress test 3</summary>

#### stress test 3 _(slow)_

- stress test 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("stress test 3")
var data = []
for i in 0..50:
    data = data.append([i, i * 2, i * 3])
check(data.len() == 50)
```

</details>


</details>

<details>
<summary>Advanced: stress test 4</summary>

#### stress test 4 _(slow)_

- stress test 4


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("stress test 4")
var dict = {}
for i in 0..100:
    dict["key_" + str(i)] = i
check(dict.keys().len() == 100)
```

</details>


</details>

<details>
<summary>Advanced: stress test 5</summary>

#### stress test 5 _(slow)_

- stress test 5


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("stress test 5")
var nested = []
for i in 0..20:
    var inner = []
    for j in 0..20:
        inner = inner.append(i * j)
    nested = nested.append(inner)
check(nested.len() == 20)
```

</details>


</details>

<details>
<summary>Advanced: stress test 6</summary>

#### stress test 6 _(slow)_

- stress test 6


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("stress test 6")
var result = ""
for i in 0..100:
    result = result + "x"
check(result.len() == 100)
```

</details>


</details>

<details>
<summary>Advanced: stress test 7</summary>

#### stress test 7 _(slow)_

- stress test 7


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("stress test 7")
var processed = []
for i in 0..200:
    if i % 2 == 0:
        processed = processed.append(i)
check(processed.len() == 100)
```

</details>


</details>

<details>
<summary>Advanced: stress test 8</summary>

#### stress test 8 _(slow)_

- stress test 8


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("stress test 8")
var count = 0
for i in 0..10:
    for j in 0..10:
        for k in 0..10:
            count = count + 1
check(count == 1000)
```

</details>


</details>

<details>
<summary>Advanced: memory stress</summary>

#### memory stress _(slow)_

- memory stress


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("memory stress")
var data = []
for i in 0..100:
    data = data.append({"id": i, "data": [1, 2, 3, 4, 5]})
check(data.len() == 100)
```

</details>


</details>

<details>
<summary>Advanced: combined stress</summary>

#### combined stress _(slow)_

- combined stress


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("combined stress")
var final = []
for i in 0..50:
    var temp = []
    for j in 0..50:
        temp = temp.append(i + j)
    var sum = 0
    for x in temp:
        sum = sum + x
    final = final.append(sum)
check(final.len() == 50)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 10 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `583e3b0e3c2798381448d71257769b7c19b1fca45089aa29d1b5288d1168b2bd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `583e3b0e3c2798381448d71257769b7c19b1fca45089aa29d1b5288d1168b2bd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `583e3b0e3c2798381448d71257769b7c19b1fca45089aa29d1b5288d1168b2bd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/05_perf/stress/file_stress_large_spec.spl
mirror: doc/06_spec/05_perf/stress/file_stress_large_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/stress/file_stress_large_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/stress/file_stress_large_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/stress/file_stress_large_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stress test 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/stress/file_stress_large_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stress test 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/stress/file_stress_large_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stress test 3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
