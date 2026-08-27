# Final System Test

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Final System Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #FINAL |
| Category | Testing |
| Status | Implemented |
| Source | `test/03_system/feature/final_push/final_push_22_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Final System Test

<details>
<summary>Advanced: complete system check 1</summary>

#### complete system check 1 _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- complete system check 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("complete system check 1")
val result = 1 + 1
verify(result == 2)
```

</details>


</details>

<details>
<summary>Advanced: complete system check 2</summary>

#### complete system check 2 _(slow)_

- complete system check 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("complete system check 2")
val arr = [1, 2, 3, 4, 5]
var sum = 0
for x in arr:
    sum = sum + x
verify(sum == 15)
```

</details>


</details>

<details>
<summary>Advanced: complete system check 3</summary>

#### complete system check 3 _(slow)_

- complete system check 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("complete system check 3")
val opt = Some(100)
match opt:
    Some(x): verify(x == 100)
    nil: verify(false)
```

</details>


</details>

<details>
<summary>Advanced: complete system check 4</summary>

#### complete system check 4 _(slow)_

- complete system check 4


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("complete system check 4")
var state = "start"
if state == "start":
    state = "processing"
if state == "processing":
    state = "done"
verify(state == "done")
```

</details>


</details>

<details>
<summary>Advanced: complete system check 5</summary>

#### complete system check 5 _(slow)_

- complete system check 5


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("complete system check 5")
val dict = {"a": 1, "b": 2, "c": 3}
val keys = dict.keys()
verify(keys.len() == 3)
```

</details>


</details>

<details>
<summary>Advanced: complete system check 6</summary>

#### complete system check 6 _(slow)_

- complete system check 6


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("complete system check 6")
var count = 0
for i in 0..20:
    if i % 2 == 0:
        count = count + 1
verify(count == 10)
```

</details>


</details>

<details>
<summary>Advanced: complete system check 7</summary>

#### complete system check 7 _(slow)_

- complete system check 7


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("complete system check 7")
val nested = [[1, 2], [3, 4], [5, 6]]
verify(nested.len() == 3)
verify(nested[0].len() == 2)
```

</details>


</details>

<details>
<summary>Advanced: complete system check 8</summary>

#### complete system check 8 _(slow)_

- complete system check 8


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("complete system check 8")
val s = "test string"
verify(s.len() == 11)
verify(s.contains("test"))
```

</details>


</details>

<details>
<summary>Advanced: complete system check 9</summary>

#### complete system check 9 _(slow)_

- complete system check 9


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("complete system check 9")
val a = 10
val b = 20
verify(a < b)
verify(b > a)
verify(a + b == 30)
```

</details>


</details>

<details>
<summary>Advanced: complete system check 10</summary>

#### complete system check 10 _(slow)_

- complete system check 10


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("complete system check 10")
var results = []
for i in 0..5:
    results = results.append(i * i)
verify(results.len() == 5)
verify(results[4] == 16)
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c012bc6f4ae80fda1b8dabc3a5396bdfc7f5ae8f48fdb1be36f5edcc2e7973be`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c012bc6f4ae80fda1b8dabc3a5396bdfc7f5ae8f48fdb1be36f5edcc2e7973be`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c012bc6f4ae80fda1b8dabc3a5396bdfc7f5ae8f48fdb1be36f5edcc2e7973be`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/final_push/final_push_22_system_spec.spl
mirror: doc/06_spec/03_system/feature/final_push/final_push_22_system_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/final_push/final_push_22_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/final_push/final_push_22_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/final_push/final_push_22_system_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'complete system check 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/final_push/final_push_22_system_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'complete system check 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/final_push/final_push_22_system_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'complete system check 3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
