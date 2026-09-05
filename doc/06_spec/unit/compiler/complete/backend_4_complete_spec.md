# COMPILER Module Complete Test

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# COMPILER Module Complete Test

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/complete/backend_4_complete_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### COMPILER Complete Coverage

#### compilation path 1

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compilation path 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compilation path 1")
check(true)
```

</details>

#### compilation path 2

- compilation path 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compilation path 2")
val code = "fn test(): pass"
check(code.contains("fn"))
```

</details>

#### type checking 1

- type checking 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type checking 1")
val x = 5
check(x > 0)
```

</details>

#### type checking 2

- type checking 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type checking 2")
val arr = [1, 2, 3]
check(arr.len() == 3)
```

</details>

#### optimization 1

- optimization 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optimization 1")
val result = 1 + 1
check(result == 2)
```

</details>

#### error path 1

- error path 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error path 1")
var error = nil
check(error == nil)
```

</details>

#### error path 2

- error path 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error path 2")
val opt = nil
check(not opt.?)
```

</details>

#### edge case 1

- edge case 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("edge case 1")
val empty = []
check(empty.len() == 0)
```

</details>

#### branch 1

- branch 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("branch 1")
if true: check(true)
else: check(false)
```

</details>

#### branch 2

- branch 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("branch 2")
val x = 10
val result = if x > 5: "big" else: "small"
check(result == "big")
```

</details>

<details>
<summary>Advanced: loop 1</summary>

#### loop 1

- loop 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loop 1")
var count = 0
for i in 0..10:
    count = count + 1
check(count == 10)
```

</details>


</details>

#### match 1

- match 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match 1")
match Some(42):
    Some(x): check(x == 42)
    nil: check(false)
```

</details>

#### nested 1

- nested 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested 1")
if true:
    if true: check(true)
    else: check(false)
else: check(false)
```

</details>

#### pipeline 1

- pipeline 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pipeline 1")
val stage1 = "input"
val stage2 = stage1 + "_processed"
check(stage2 == "input_processed")
```

</details>

#### integration 1

- integration 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integration 1")
val dict = {"compile": "success"}
check(dict["compile"] == "success")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `b419618a030308704a27df592a0b7bdb256b474ee4a52b6d6542e5199bc9ec11`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b419618a030308704a27df592a0b7bdb256b474ee4a52b6d6542e5199bc9ec11`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b419618a030308704a27df592a0b7bdb256b474ee4a52b6d6542e5199bc9ec11`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/complete/backend_4_complete_spec.spl
mirror: doc/06_spec/unit/compiler/complete/backend_4_complete_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/complete/backend_4_complete_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/complete/backend_4_complete_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/complete/backend_4_complete_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compilation path 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/complete/backend_4_complete_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compilation path 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/complete/backend_4_complete_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'type checking 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
