# STDLIB Module Complete Test

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# STDLIB Module Complete Test

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/std/complete/fs_5_complete_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### STDLIB Complete Coverage

#### public API 1

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- public API 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("public API 1")
verify(true)
```

</details>

#### public API 2

- public API 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("public API 2")
verify(1 + 1 == 2)
```

</details>

#### public API 3

- public API 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("public API 3")
val x = "test"
verify(x.len() == 4)
```

</details>

#### public API 4

- public API 4


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("public API 4")
val arr = [1, 2, 3]
verify(arr.len() == 3)
```

</details>

#### public API 5

- public API 5


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("public API 5")
for i in 0..5:
    verify(i >= 0)
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
val opt = nil
verify(not opt.?)
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
val arr = []
verify(arr.len() == 0)
```

</details>

#### edge case 1

- edge case 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("edge case 1")
verify(0 == 0)
```

</details>

#### edge case 2

- edge case 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("edge case 2")
val s = ""
verify(s.len() == 0)
```

</details>

#### branch 1

- branch 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("branch 1")
if true:
    verify(true)
else:
    verify(false)
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
match Some(1):
    Some(x): verify(x == 1)
    nil: verify(false)
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
var sum = 0
for i in 0..5:
    sum = sum + i
verify(sum == 10)
```

</details>


</details>

#### nested 1

- nested 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested 1")
if true:
    if true:
        verify(true)
    else:
        verify(false)
else:
    verify(false)
```

</details>

#### complex 1

- complex 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("complex 1")
val arr = [1, 2, 3, 4, 5]
var evens = []
for x in arr:
    if x % 2 == 0:
        evens = evens.append(x)
verify(evens.len() == 2)
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
val data = {"key": "value"}
verify(data["key"] == "value")
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

- Canonical SPipe generation for source `3d4ec83c49fd1c77259698a952bd4188b7b611baa00361b88551fdd3aa66a2ad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3d4ec83c49fd1c77259698a952bd4188b7b611baa00361b88551fdd3aa66a2ad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3d4ec83c49fd1c77259698a952bd4188b7b611baa00361b88551fdd3aa66a2ad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/std/complete/fs_5_complete_spec.spl
mirror: doc/06_spec/unit/std/complete/fs_5_complete_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/std/complete/fs_5_complete_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/std/complete/fs_5_complete_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/std/complete/fs_5_complete_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'public API 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/std/complete/fs_5_complete_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'public API 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/std/complete/fs_5_complete_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'public API 3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
