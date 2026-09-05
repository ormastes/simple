# Method Call Inference Specification

> Tests covering HIR method-call inference aggregate transport.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Method Call Inference Specification

## Scenarios

### HIR method-call inference aggregate transport

#### infers every argument in a nested method-call payload

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- infers every argument in a nested method-call payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers every argument in a nested method-call payload")
var ctx = HmInferContext.new()
val inner = unresolved_method(method_int(1), "inner", [method_arg(method_int(2))])
val outer = unresolved_method(
    method_int(3),
    "outer",
    [method_arg(inner), method_arg(method_int(4))]
)

val inferred = ctx.synthesize_expr(outer)
expect(inferred.is_ok()).to_be(true)
expect(type_is_infer(inferred.unwrap())).to_be(true)
```

</details>

#### visits an argument nested inside another method call

- visits an argument nested inside another method call


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("visits an argument nested inside another method call")
var ctx = HmInferContext.new()
val inner = unresolved_method(
    method_int(1),
    "inner",
    [method_arg(method_undefined(901))]
)
val outer = unresolved_method(method_int(2), "outer", [method_arg(inner)])

val inferred = ctx.synthesize_expr(outer)
expect(inferred.is_ok()).to_be(false)
val error = inferred.err.unwrap()
expect(error_is_undefined(error)).to_be(true)
expect(error.message()).to_contain("901")
```

</details>

#### visits a later argument after a valid nested argument

- visits a later argument after a valid nested argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("visits a later argument after a valid nested argument")
var ctx = HmInferContext.new()
val inner = unresolved_method(method_int(1), "inner", [method_arg(method_int(2))])
val outer = unresolved_method(
    method_int(3),
    "outer",
    [method_arg(inner), method_arg(method_undefined(902))]
)

val inferred = ctx.synthesize_expr(outer)
expect(inferred.is_ok()).to_be(false)
val error = inferred.err.unwrap()
expect(error_is_undefined(error)).to_be(true)
expect(error.message()).to_contain("902")
```

</details>

#### keeps an unresolved method fail-closed for effects

- keeps an unresolved method fail-closed for effects


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps an unresolved method fail-closed for effects")
var ctx = HmInferContext.new()
val pure_call = unresolved_method(method_int(1), "pure", [method_arg(method_int(2))])
val effects = ctx.infer_expr_effects(pure_call)
var has_io = false
for effect in effects:
    if effect_is_io(effect):
        has_io = true
expect(has_io).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/type_infer/method_call_inference_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HIR method-call inference aggregate transport.
- HIR method-call inference aggregate transport

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `a9b29d8a545a9c9dea8d50f6107cfee9430b95eca4f26198616c8be5774ca429`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a9b29d8a545a9c9dea8d50f6107cfee9430b95eca4f26198616c8be5774ca429`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a9b29d8a545a9c9dea8d50f6107cfee9430b95eca4f26198616c8be5774ca429`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/type_infer/method_call_inference_spec.spl
mirror: doc/06_spec/01_unit/compiler/type_infer/method_call_inference_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/type_infer/method_call_inference_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/type_infer/method_call_inference_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/type_infer/method_call_inference_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infers every argument in a nested method-call payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/type_infer/method_call_inference_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'visits an argument nested inside another method call' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/type_infer/method_call_inference_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'visits a later argument after a valid nested argument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
