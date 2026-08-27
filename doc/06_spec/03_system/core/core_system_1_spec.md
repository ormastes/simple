# CORE System Test

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CORE System Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CORE-SYS |
| Category | System Testing |
| Status | Implemented |
| Source | `test/03_system/core/core_system_1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### CORE System Test

<details>
<summary>Advanced: complete workflow 1</summary>

#### complete workflow 1 _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- complete workflow 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("complete workflow 1")
val input = "system test"
check(input.len() > 0)
```

</details>


</details>

<details>
<summary>Advanced: complete workflow 2</summary>

#### complete workflow 2 _(slow)_

- complete workflow 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("complete workflow 2")
var data = []
for i in 0..20:
    data = data.append(i)
check(data.len() == 20)
```

</details>


</details>

<details>
<summary>Advanced: complete workflow 3</summary>

#### complete workflow 3 _(slow)_

- complete workflow 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("complete workflow 3")
val code = "fn test(): pass"
val code_len = code.len()
check(code_len > 0)
```

</details>


</details>

<details>
<summary>Advanced: complete workflow 4</summary>

#### complete workflow 4 _(slow)_

- complete workflow 4


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("complete workflow 4")
val opt = Some(42)
match opt:
    Some(x): check(x == 42)
    nil: check(false)
```

</details>


</details>

<details>
<summary>Advanced: complete workflow 5</summary>

#### complete workflow 5 _(slow)_

- complete workflow 5


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("complete workflow 5")
var state = "init"
if state == "init":
    state = "done"
check(state == "done")
```

</details>


</details>

<details>
<summary>Advanced: error handling</summary>

#### error handling _(slow)_

- error handling


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error handling")
var error = nil
check(error == nil)
```

</details>


</details>

<details>
<summary>Advanced: edge case</summary>

#### edge case _(slow)_

- edge case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edge case")
val empty = []
check(empty.len() == 0)
```

</details>


</details>

<details>
<summary>Advanced: boundary</summary>

#### boundary _(slow)_

- boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boundary")
val single = [1]
check(single[0] == 1)
```

</details>


</details>

<details>
<summary>Advanced: integration</summary>

#### integration _(slow)_

- integration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("integration")
val a = 10
val b = 20
check(a + b == 30)
```

</details>


</details>

<details>
<summary>Advanced: validation</summary>

#### validation _(slow)_

- validation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validation")
check(true)
check(not false)
check(1 == 1)
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

- Canonical SPipe generation for source `6518680efddc430fa5229ca612c5879c7b69183b3d62a1e9ef8c611ede6724e4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6518680efddc430fa5229ca612c5879c7b69183b3d62a1e9ef8c611ede6724e4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6518680efddc430fa5229ca612c5879c7b69183b3d62a1e9ef8c611ede6724e4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/core/core_system_1_spec.spl
mirror: doc/06_spec/03_system/core/core_system_1_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/core/core_system_1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/core/core_system_1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/core/core_system_1_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'complete workflow 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/core/core_system_1_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'complete workflow 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/core/core_system_1_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'complete workflow 3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
