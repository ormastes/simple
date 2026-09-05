# CORE Integration Test

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CORE Integration Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CORE-INT |
| Category | Integration Testing |
| Status | Implemented |
| Source | `test/integration/core/core_integration_42_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### CORE Integration

#### lexer to parser

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lexer to parser


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("lexer to parser")
val code = "val x = 42"
check(code.contains("val"))
```

</details>

#### parser to AST

- parser to AST


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parser to AST")

val code = "fn foo(): pass"
check(code.contains("fn"))
```

</details>

#### AST to MIR

- AST to MIR


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AST to MIR")

val code = "x + y"
check(code.contains("+"))
```

</details>

#### MIR to backend

- MIR to backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("MIR to backend")

val code = "1 + 2"
check(code.len() > 0)
```

</details>

#### end-to-end pipeline

- end-to-end pipeline


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("end-to-end pipeline")

val input = "test"
val result = input + "_processed"
check(result == "test_processed")
```

</details>

#### error recovery

- error recovery


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("error recovery")

var error = nil
if error == nil:
    check(true)
else:
    check(false)
```

</details>

#### type checking

- type checking


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("type checking")

val x = 5
check(x > 0)
```

</details>

#### interpreter integration

- interpreter integration


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("interpreter integration")

val arr = [1, 2, 3]
var sum = 0
for x in arr:
    sum = sum + x
check(sum == 6)
```

</details>

#### value representation

- value representation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("value representation")

val opt = Some(100)
check(opt.?)
check(opt? == 100)
```

</details>

#### environment handling

- environment handling


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("environment handling")

val dict = {"key": "value"}
check(dict["key"] == "value")
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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5d39ea9c45992fbd6fc1bca6ca7e894206cca293773908f253e795c7f7f0b5e4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5d39ea9c45992fbd6fc1bca6ca7e894206cca293773908f253e795c7f7f0b5e4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5d39ea9c45992fbd6fc1bca6ca7e894206cca293773908f253e795c7f7f0b5e4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/core/core_integration_42_spec.spl
mirror: doc/06_spec/integration/core/core_integration_42_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/core/core_integration_42_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/core/core_integration_42_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/core/core_integration_42_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lexer to parser' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/core/core_integration_42_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parser to AST' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/core/core_integration_42_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AST to MIR' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
