# System Test - Full Integration

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# System Test - Full Integration

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYSTEM |
| Category | Testing |
| Status | Implemented |
| Source | `test/03_system/e2e/functional/functional_4_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### System Level Test

<details>
<summary>Advanced: end-to-end workflow</summary>

#### end-to-end workflow _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- end-to-end workflow


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("end-to-end workflow")
val input = "system test input"
verify(input.len() > 0)

var processed = input
for i in 0..5:
    processed = processed + "_step{i}"

verify(processed.contains("step"))
```

</details>


</details>

<details>
<summary>Advanced: integration point 1</summary>

#### integration point 1 _(slow)_

- integration point 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("integration point 1")
var data = []
for i in 0..30:
    data = data.append(i)

var sum = 0
for d in data:
    sum = sum + d

verify(sum == 435)
```

</details>


</details>

<details>
<summary>Advanced: integration point 2</summary>

#### integration point 2 _(slow)_

- integration point 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("integration point 2")
val a = 1
val b = 2
val c = 3
val total = a + b + c
verify(total == 6)
```

</details>


</details>

<details>
<summary>Advanced: full stack test</summary>

#### full stack test _(slow)_

- full stack test


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("full stack test")
# Bottom layer
val base = [1, 2, 3]

# Middle layer
var processed = []
for b in base:
    processed = processed.append(b * 2)

# Top layer
var sum = 0
for p in processed:
    sum = sum + p

verify(sum == 12)
```

</details>


</details>

<details>
<summary>Advanced: boundary condition test</summary>

#### boundary condition test _(slow)_

- boundary condition test


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boundary condition test")
val cases = [0, 1, -1, 100, -100]

for c in cases:
    val result = if c > 0: "positive"
                elif c < 0: "negative"
                else: "zero"
    verify(result.len() > 0)
```

</details>


</details>

<details>
<summary>Advanced: error handling test</summary>

#### error handling test _(slow)_

- error handling test


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error handling test")
var errors = []

for i in 0..10:
    if i == 5:
        errors = errors.append("error at 5")

verify(errors.len() == 1)
```

</details>


</details>

<details>
<summary>Advanced: recovery test</summary>

#### recovery test _(slow)_

- recovery test


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("recovery test")
var state = "normal"

# Simulate error
state = "error"

# Recover
if state == "error":
    state = "recovered"

verify(state == "recovered")
```

</details>


</details>

<details>
<summary>Advanced: complex scenario</summary>

#### complex scenario _(slow)_

- complex scenario


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("complex scenario")
var results = []

for outer in 0..5:
    var inner_sum = 0
    for inner in 0..5:
        inner_sum = inner_sum + inner
    results = results.append(inner_sum)

verify(results.len() == 5)
```

</details>


</details>

<details>
<summary>Advanced: data flow test</summary>

#### data flow test _(slow)_

- data flow test


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("data flow test")
val source = "data"
val stage1 = source + "_1"
val stage2 = stage1 + "_2"
val stage3 = stage2 + "_3"
val final = stage3 + "_final"

verify(final == "data_1_2_3_final")
```

</details>


</details>

<details>
<summary>Advanced: state transition</summary>

#### state transition _(slow)_

- state transition


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("state transition")
var state = 0

for i in 0..10:
    if state == 0:
        state = 1
    elif state == 1:
        state = 2
    else:
        state = 0

verify(state >= 0)
```

</details>


</details>

<details>
<summary>Advanced: validation chain</summary>

#### validation chain _(slow)_

- validation chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validation chain")
val valid1 = true
val valid2 = true
val valid3 = true

val all_valid = valid1 and valid2 and valid3
verify(all_valid)
```

</details>


</details>

<details>
<summary>Advanced: pipeline test</summary>

#### pipeline test _(slow)_

- pipeline test


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pipeline test")
val input = [1, 2, 3, 4, 5]

# Stage 1: filter
var filtered = []
for x in input:
    if x % 2 == 0:
        filtered = filtered.append(x)

# Stage 2: transform
var transformed = []
for f in filtered:
    transformed = transformed.append(f * 10)

verify(transformed.len() == 2)
```

</details>


</details>

<details>
<summary>Advanced: comprehensive check</summary>

#### comprehensive check _(slow)_

- comprehensive check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("comprehensive check")
var checks = 0

if 1 == 1:
    checks = checks + 1
if 2 > 1:
    checks = checks + 1
if 3 < 4:
    checks = checks + 1
if true:
    checks = checks + 1
if not false:
    checks = checks + 1

verify(checks == 5)
```

</details>


</details>

<details>
<summary>Advanced: resource lifecycle</summary>

#### resource lifecycle _(slow)_

- resource lifecycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resource lifecycle")
var resource = "allocated"
verify(resource.len() > 0)

# Use resource
val used = resource + "_used"
verify(used.contains("used"))

# Release
resource = ""
verify(resource.len() == 0)
```

</details>


</details>

<details>
<summary>Advanced: complex condition</summary>

#### complex condition _(slow)_

- complex condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("complex condition")
val a = 10
val b = 20
val c = 30

if a < b:
    if b < c:
        if a + b <= c:
            verify(true)
        else:
            verify(false)
    else:
        verify(false)
else:
    verify(false)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 15 |
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

- Canonical SPipe generation for source `d2522d33d31c45b10b3f2de8f3a237748d1217bdcba776750874d1479c7c5356`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d2522d33d31c45b10b3f2de8f3a237748d1217bdcba776750874d1479c7c5356`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d2522d33d31c45b10b3f2de8f3a237748d1217bdcba776750874d1479c7c5356`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/e2e/functional/functional_4_system_spec.spl
mirror: doc/06_spec/03_system/e2e/functional/functional_4_system_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/e2e/functional/functional_4_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/e2e/functional/functional_4_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/e2e/functional/functional_4_system_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'end-to-end workflow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/e2e/functional/functional_4_system_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'integration point 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/e2e/functional/functional_4_system_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'integration point 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
