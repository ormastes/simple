# Aop Predicate Parser Specification

> Tests covering AOP Predicate Parser, validate_predicate, validate_advice_form.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aop Predicate Parser Specification

## Scenarios

### AOP Predicate Parser

### validate_predicate

#### accepts wildcard predicate

- accepts wildcard predicate
   - Expected: validate_predicate("*") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts wildcard predicate")
expect(validate_predicate("*")).to_equal("")
```

</details>

#### accepts execution selector

- accepts execution selector
   - Expected: validate_predicate("execution(* foo(..))") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts execution selector")
expect(validate_predicate("execution(* foo(..))")).to_equal("")
```

</details>

#### accepts within selector

- accepts within selector
   - Expected: validate_predicate("within(services.*)") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts within selector")
expect(validate_predicate("within(services.*)")).to_equal("")
```

</details>

#### accepts attr selector

- accepts attr selector
   - Expected: validate_predicate("attr(logged)") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts attr selector")
expect(validate_predicate("attr(logged)")).to_equal("")
```

</details>

#### accepts AND operator

- accepts AND operator
   - Expected: validate_predicate("execution(* foo(..)) & attr(logged)") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts AND operator")
expect(validate_predicate("execution(* foo(..)) & attr(logged)")).to_equal("")
```

</details>

#### accepts OR operator

- accepts OR operator
   - Expected: validate_predicate("execution(* a(..)) | execution(* b(..))") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts OR operator")
expect(validate_predicate("execution(* a(..)) | execution(* b(..))")).to_equal("")
```

</details>

#### accepts NOT operator

- accepts NOT operator
   - Expected: validate_predicate("!execution(* skip(..))") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts NOT operator")
expect(validate_predicate("!execution(* skip(..))")).to_equal("")
```

</details>

#### accepts grouped expression

- accepts grouped expression
   - Expected: validate_predicate("(execution(*) | within(svc.*)) & attr(tx)") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts grouped expression")
expect(validate_predicate("(execution(*) | within(svc.*)) & attr(tx)")).to_equal("")
```

</details>

#### rejects empty predicate

- rejects empty predicate


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects empty predicate")
expect(validate_predicate("")).to_start_with("E1501")
```

</details>

#### rejects deferred selector get

- rejects deferred selector get


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects deferred selector get")
expect(validate_predicate("get(field)")).to_start_with("E1507")
```

</details>

#### rejects deferred selector set

- rejects deferred selector set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects deferred selector set")
expect(validate_predicate("set(field)")).to_start_with("E1507")
```

</details>

#### rejects deferred selector init

- rejects deferred selector init


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects deferred selector init")
expect(validate_predicate("init(Type)")).to_start_with("E1507")
```

</details>

#### rejects deferred selector effect

- rejects deferred selector effect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects deferred selector effect")
expect(validate_predicate("effect(io)")).to_start_with("E1507")
```

</details>

#### rejects unknown selector

- rejects unknown selector


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unknown selector")
expect(validate_predicate("foobar(x)")).to_start_with("E1507")
```

</details>

#### rejects unmatched parenthesis

- rejects unmatched parenthesis


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unmatched parenthesis")
expect(validate_predicate("execution(* foo(..")).to_start_with("E1501")
```

</details>

### validate_advice_form

#### accepts before

- accepts before
   - Expected: validate_advice_form("before") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts before")
expect(validate_advice_form("before")).to_equal("")
```

</details>

#### accepts after_success

- accepts after_success
   - Expected: validate_advice_form("after_success") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts after_success")
expect(validate_advice_form("after_success")).to_equal("")
```

</details>

#### accepts after_error

- accepts after_error
   - Expected: validate_advice_form("after_error") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts after_error")
expect(validate_advice_form("after_error")).to_equal("")
```

</details>

#### accepts around

- accepts around
   - Expected: validate_advice_form("around") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts around")
expect(validate_advice_form("around")).to_equal("")
```

</details>

#### rejects invalid form

- rejects invalid form


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid form")
expect(validate_advice_form("invalid")).to_start_with("E1503")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/aop_predicate_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AOP Predicate Parser, validate_predicate, validate_advice_form.
- AOP Predicate Parser
- validate_predicate
- validate_advice_form

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `4d837d58868480b7c288d77662eecae4259d58e8bed2129ae16837ba72bbb191`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4d837d58868480b7c288d77662eecae4259d58e8bed2129ae16837ba72bbb191`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4d837d58868480b7c288d77662eecae4259d58e8bed2129ae16837ba72bbb191`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/frontend/aop_predicate_parser_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/aop_predicate_parser_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/aop_predicate_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/aop_predicate_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/aop_predicate_parser_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts wildcard predicate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/aop_predicate_parser_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts execution selector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/aop_predicate_parser_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts within selector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
