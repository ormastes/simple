# Bidir Check Specification

> Tests covering synthesize_expr, check_expr, infer_expr_bidir, check_subsumes, lambda inference with bidirectional, bidirectional error messages.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bidir Check Specification

## Scenarios

### synthesize_expr

#### synthesizes integer literal type

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- synthesizes integer literal type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("synthesizes integer literal type")
# synthesize(42) => i64
pass
```

</details>

#### synthesizes boolean literal type

- synthesizes boolean literal type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("synthesizes boolean literal type")
# synthesize(true) => bool
pass
```

</details>

#### synthesizes string literal type

- synthesizes string literal type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("synthesizes string literal type")
# synthesize("hello") => text
pass
```

</details>

#### synthesizes array literal type

- synthesizes array literal type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("synthesizes array literal type")
# synthesize([1, 2, 3]) => [i64]
pass
```

</details>

#### synthesizes lambda with inferred params

- synthesizes lambda with inferred params


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("synthesizes lambda with inferred params")
# synthesize(\x: x + 1) => fn(Infer) -> Infer
# Without expected type, params are fresh type vars
pass
```

</details>

### check_expr

#### checks literal against matching type

- checks literal against matching type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks literal against matching type")
# check(42, i64) => Ok
pass
```

</details>

#### rejects literal against mismatched type

- rejects literal against mismatched type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects literal against mismatched type")
# check(42, text) => Err(Mismatch)
pass
```

</details>

#### propagates function type into lambda params

- propagates function type into lambda params


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagates function type into lambda params")
# check(\x: x + 1, fn(i64) -> i64) => Ok
# x is inferred as i64 from expected type
pass
```

</details>

#### checks lambda body against expected return type

- checks lambda body against expected return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks lambda body against expected return type")
# check(\x: x, fn(i64) -> i64) => Ok
# check(\x: "hello", fn(i64) -> i64) => Err
pass
```

</details>

#### rejects lambda with wrong arity

- rejects lambda with wrong arity


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects lambda with wrong arity")
# check(\x, y: x + y, fn(i64) -> i64) => Err
# Expected 1 param, got 2
pass
```

</details>

#### handles nested lambdas with expected type

- handles nested lambdas with expected type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nested lambdas with expected type")
# check(\f: \x: f(x), fn(fn(i64) -> i64) -> fn(i64) -> i64) => Ok
pass
```

</details>

### infer_expr_bidir

#### dispatches to synthesize in Synthesize mode

- dispatches to synthesize in Synthesize mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches to synthesize in Synthesize mode")
# infer_expr_bidir(42, Synthesize) => Ok(i64)
pass
```

</details>

#### dispatches to check in Check mode

- dispatches to check in Check mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches to check in Check mode")
# infer_expr_bidir(42, Check(i64)) => Ok(i64)
pass
```

</details>

#### returns expected type after successful check

- returns expected type after successful check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns expected type after successful check")
# infer_expr_bidir(\x: x, Check(fn(i64) -> i64)) => Ok(fn(i64) -> i64)
pass
```

</details>

#### propagates error from failed check

- propagates error from failed check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagates error from failed check")
# infer_expr_bidir(42, Check(text)) => Err
pass
```

</details>

### check_subsumes

#### accepts identical types

- accepts identical types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts identical types")
# check_subsumes(i64, i64) => Ok
pass
```

</details>

#### accepts type variables that unify

- accepts type variables that unify


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts type variables that unify")
# check_subsumes(T, i64) => Ok (T unified to i64)
pass
```

</details>

#### rejects incompatible types

- rejects incompatible types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects incompatible types")
# check_subsumes(i64, text) => Err
pass
```

</details>

### lambda inference with bidirectional

#### infers lambda param from function argument position

- infers lambda param from function argument position


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers lambda param from function argument position")
# fn apply(f: fn(i64) -> i64, x: i64): f(x)
# apply(\y: y * 2, 5) => y inferred as i64
pass
```

</details>

#### infers lambda param from assignment context

- infers lambda param from assignment context


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers lambda param from assignment context")
# val double: fn(i64) -> i64 = \x: x * 2
# x inferred as i64
pass
```

</details>

#### infers lambda param from return position

- infers lambda param from return position


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers lambda param from return position")
# fn make_adder() -> fn(i64) -> i64:
#     \x: x + 1
# x inferred as i64
pass
```

</details>

#### chains bidirectional inference through multiple lambdas

- chains bidirectional inference through multiple lambdas


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chains bidirectional inference through multiple lambdas")
# val compose: fn(fn(i64) -> i64, fn(i64) -> i64) -> fn(i64) -> i64
# compose(\x: x + 1, \y: y * 2)
# Both x and y inferred as i64
pass
```

</details>

### bidirectional error messages

#### reports expected vs found in check mode

- reports expected vs found in check mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports expected vs found in check mode")
# check(42, text) => "expected text, found i64"
pass
```

</details>

#### reports arity mismatch for lambdas

- reports arity mismatch for lambdas


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports arity mismatch for lambdas")
# check(\x, y: x, fn(i64) -> i64) => "arity mismatch"
pass
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/type_inference/bidir_check_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering synthesize_expr, check_expr, infer_expr_bidir, check_subsumes, lambda inference with bidirectional, bidirectional error messages.
- synthesize_expr
- check_expr
- infer_expr_bidir
- check_subsumes
- lambda inference with bidirectional
- bidirectional error messages

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
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

- Canonical SPipe generation for source `9bb7f97065cca84c833e9cfa22ed6aff1b2536b355254d27057ba45926d8e9a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9bb7f97065cca84c833e9cfa22ed6aff1b2536b355254d27057ba45926d8e9a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9bb7f97065cca84c833e9cfa22ed6aff1b2536b355254d27057ba45926d8e9a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/type_inference/bidir_check_spec.spl
mirror: doc/06_spec/unit/compiler/type_inference/bidir_check_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/type_inference/bidir_check_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/type_inference/bidir_check_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/type_inference/bidir_check_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'synthesizes integer literal type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/type_inference/bidir_check_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'synthesizes boolean literal type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/type_inference/bidir_check_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'synthesizes string literal type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
