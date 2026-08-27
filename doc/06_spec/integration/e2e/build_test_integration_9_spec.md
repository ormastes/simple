# Integration & E2E Test

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Integration & E2E Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTEGRATION |
| Category | End-to-End Testing |
| Status | Implemented |
| Source | `test/integration/e2e/build_test_integration_9_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Integration Test Scenario

<details>
<summary>Advanced: e2e workflow 1</summary>

#### e2e workflow 1 _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- e2e workflow 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("e2e workflow 1")
val input = "source code"
val stage1 = input + " -> parsed"
val stage2 = stage1 + " -> typed"
val stage3 = stage2 + " -> compiled"
check(stage3.contains("compiled"))
```

</details>


</details>

<details>
<summary>Advanced: e2e workflow 2</summary>

#### e2e workflow 2 _(slow)_

- e2e workflow 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("e2e workflow 2")
val data = [1, 2, 3, 4, 5]
var processed = []
for x in data:
    processed = processed.append(x * 2)
var sum = 0
for x in processed:
    sum = sum + x
check(sum == 30)
```

</details>


</details>

<details>
<summary>Advanced: e2e workflow 3</summary>

#### e2e workflow 3 _(slow)_

- e2e workflow 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("e2e workflow 3")
val config = {"input": "test.spl", "output": "test.out"}
val input_file = config["input"]
val output_file = config["output"]
check(input_file.ends_with(".spl"))
check(output_file.ends_with(".out"))
```

</details>


</details>

<details>
<summary>Advanced: error propagation</summary>

#### error propagation _(slow)_

- error propagation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("error propagation")
var error = nil
if error == nil:
    check(true)
else:
    check(false)
```

</details>


</details>

<details>
<summary>Advanced: state transitions</summary>

#### state transitions _(slow)_

- state transitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("state transitions")
var state = "init"
if state == "init":
    state = "processing"
if state == "processing":
    state = "complete"
check(state == "complete")
```

</details>


</details>

<details>
<summary>Advanced: data pipeline</summary>

#### data pipeline _(slow)_

- data pipeline


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("data pipeline")
val raw = [1, 2, 3, 4, 5]
var filtered = []
for x in raw:
    if x % 2 == 0:
        filtered = filtered.append(x)
var transformed = []
for x in filtered:
    transformed = transformed.append(x * 10)
check(transformed.len() == 2)
```

</details>


</details>

<details>
<summary>Advanced: module interaction</summary>

#### module interaction _(slow)_

- module interaction


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("module interaction")
val module_a = {"export": "value_a"}
val module_b = {"import": module_a["export"]}
check(module_b["import"] == "value_a")
```

</details>


</details>

<details>
<summary>Advanced: nested processing</summary>

#### nested processing _(slow)_

- nested processing


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("nested processing")
val outer = [[1, 2], [3, 4], [5, 6]]
var flattened = []
for inner in outer:
    for x in inner:
        flattened = flattened.append(x)
check(flattened.len() == 6)
```

</details>


</details>

<details>
<summary>Advanced: error recovery flow</summary>

#### error recovery flow _(slow)_

- error recovery flow


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("error recovery flow")
val opt = nil
val result = opt ?? "default"
check(result == "default")
```

</details>


</details>

<details>
<summary>Advanced: full validation</summary>

#### full validation _(slow)_

- full validation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("full validation")
val input = [1, 2, 3, 4, 5]
var validated = true
for x in input:
    if x <= 0:
        validated = false
check(validated)
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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `20ff915d673d442bbaffcf6e3b7c5bbf9d7128181d156ccee6ad3420598b636a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `20ff915d673d442bbaffcf6e3b7c5bbf9d7128181d156ccee6ad3420598b636a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `20ff915d673d442bbaffcf6e3b7c5bbf9d7128181d156ccee6ad3420598b636a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/e2e/build_test_integration_9_spec.spl
mirror: doc/06_spec/integration/e2e/build_test_integration_9_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/e2e/build_test_integration_9_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/e2e/build_test_integration_9_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/e2e/build_test_integration_9_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'e2e workflow 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/e2e/build_test_integration_9_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'e2e workflow 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/e2e/build_test_integration_9_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'e2e workflow 3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
