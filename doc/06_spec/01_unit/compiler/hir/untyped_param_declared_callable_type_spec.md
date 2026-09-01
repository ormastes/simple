# Untyped Param Declared Callable Type Specification

> Tests covering declared_callable_type tolerates untyped parameters.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Untyped Param Declared Callable Type Specification

## Scenarios

### declared_callable_type tolerates untyped parameters

#### lowers a free function with a fully untyped parameter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lowers a free function with a fully untyped parameter
   - Expected: untyped_param_free_fn(1) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers a free function with a fully untyped parameter")
expect(untyped_param_free_fn(1)).to_equal(2)
```

</details>

#### lowers a function mixing untyped and typed parameters

- lowers a function mixing untyped and typed parameters
   - Expected: untyped_param_mixed(2, 3) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers a function mixing untyped and typed parameters")
expect(untyped_param_mixed(2, 3)).to_equal(5)
```

</details>

#### lowers an untyped-parameter function with no declared return type

- lowers an untyped-parameter function with no declared return type
   - Expected: untyped_param_no_return(7) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers an untyped-parameter function with no declared return type")
expect(untyped_param_no_return(7)).to_equal(7)
```

</details>

#### lowers a method with an untyped parameter

- lowers a method with an untyped parameter
   - Expected: holder.add_untyped(5) equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers a method with an untyped parameter")
val holder = UntypedParamHolder()
expect(holder.add_untyped(5)).to_equal(15)
```

</details>

#### lowers a static function with an untyped parameter

- lowers a static function with an untyped parameter
   - Expected: UntypedParamHolder.static_untyped(4) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers a static function with an untyped parameter")
expect(UntypedParamHolder.static_untyped(4)).to_equal(8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/untyped_param_declared_callable_type_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering declared_callable_type tolerates untyped parameters.
- declared_callable_type tolerates untyped parameters

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `da2e23fa9c03e15538873ed30ca88affe1c9101c7b0da001003042cf01514105`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `da2e23fa9c03e15538873ed30ca88affe1c9101c7b0da001003042cf01514105`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `da2e23fa9c03e15538873ed30ca88affe1c9101c7b0da001003042cf01514105`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/hir/untyped_param_declared_callable_type_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/untyped_param_declared_callable_type_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/untyped_param_declared_callable_type_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/untyped_param_declared_callable_type_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/untyped_param_declared_callable_type_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/untyped_param_declared_callable_type_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers a free function with a fully untyped parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/untyped_param_declared_callable_type_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers a function mixing untyped and typed parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/untyped_param_declared_callable_type_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers an untyped-parameter function with no declared return type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
