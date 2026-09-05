# CORE Interpreter Module Complete Test

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CORE Interpreter Module Complete Test

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/core/complete/interpreter_value_complete_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Interpreter Module Coverage

#### test 1

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- test 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("test 1")
check(true)
```

</details>

#### test 2

- test 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("test 2")
check(1 + 1 == 2)
```

</details>

#### test 3

- test 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("test 3")
check("a" == "a")
```

</details>

#### test 4

- test 4


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("test 4")
val x = 5
check(x > 0)
```

</details>

#### test 5

- test 5


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("test 5")
val arr = [1, 2, 3]
check(arr.len() == 3)
```

</details>

#### test 6

- test 6


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("test 6")
for i in 0..5:
    check(i >= 0)
```

</details>

#### test 7

- test 7


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("test 7")
val opt = Some(42)
check(opt.?)
```

</details>

#### test 8

- test 8


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("test 8")
match Some(1):
    Some(x): check(x == 1)
    nil: check(false)
```

</details>

#### test 9

- test 9


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("test 9")
if true:
    check(true)
else:
    check(false)
```

</details>

#### test 10

- test 10


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("test 10")
val d = {"k": "v"}
check(d["k"] == "v")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `b5194a6be3173c7af1d0ff5ee7d4ec3c1956c3437ad4f2cf87cd62827524ce46`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b5194a6be3173c7af1d0ff5ee7d4ec3c1956c3437ad4f2cf87cd62827524ce46`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b5194a6be3173c7af1d0ff5ee7d4ec3c1956c3437ad4f2cf87cd62827524ce46`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/core/complete/interpreter_value_complete_spec.spl
mirror: doc/06_spec/unit/core/complete/interpreter_value_complete_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/core/complete/interpreter_value_complete_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/core/complete/interpreter_value_complete_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/core/complete/interpreter_value_complete_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test 1' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/core/complete/interpreter_value_complete_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'test 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/core/complete/interpreter_value_complete_spec.spl:22:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test 2' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/core/complete/interpreter_value_complete_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'test 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/core/complete/interpreter_value_complete_spec.spl:26:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test 3' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/core/complete/interpreter_value_complete_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'test 3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/core/complete/interpreter_value_complete_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test 4' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/core/complete/interpreter_value_complete_spec.spl:35:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test 5' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/core/complete/interpreter_value_complete_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test 6' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
