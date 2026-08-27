# Closure Nested Typed Binding Specification

> Tests covering typed val bindings in nested closure blocks.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Closure Nested Typed Binding Specification

## Scenarios

### typed val bindings in nested closure blocks

#### binds annotated i32 inside if and reads it

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds annotated i32 inside if and reads it
   - Expected: x equals `5`
   - Expected: 2 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds annotated i32 inside if and reads it")
val cond = true
if cond:
    val x: i32 = 5
    expect(x).to_equal(5)
else:
    expect(2).to_equal(2)
```

</details>

#### binds annotated u32 inside if and passes it as call arg

- binds annotated u32 inside if and passes it as call arg
   - Expected: take_u(v) equals `0xFF0000FFu32`
   - Expected: 2 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds annotated u32 inside if and passes it as call arg")
val cond = true
if cond:
    val v: u32 = 0xFF0000FFu32
    expect(take_u(v)).to_equal(0xFF0000FFu32)
else:
    expect(2).to_equal(2)
```

</details>

#### binds annotated val inside while body

- binds annotated val inside while body
   - Expected: total equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds annotated val inside while body")
var i = 0
var total = 0
while i < 1:
    val x: i32 = 7
    total = total + x
    i = i + 1
expect(total).to_equal(7)
```

</details>

#### binds annotated val inside else branch

- binds annotated val inside else branch
   - Expected: 1 equals `1`
   - Expected: x equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds annotated val inside else branch")
val cond = false
if cond:
    expect(1).to_equal(1)
else:
    val x: i32 = 9
    expect(x).to_equal(9)
```

</details>

#### binds tuple destructuring inside if

- binds tuple destructuring inside if
   - Expected: a + b equals `7`
   - Expected: 2 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds tuple destructuring inside if")
val cond = true
if cond:
    val (a, b) = (3, 4)
    expect(a + b).to_equal(7)
else:
    expect(2).to_equal(2)
```

</details>

#### binds typed val inside Ok((a,b)) match arm body

- binds typed val inside Ok((a,b)) match arm body
   - Expected: joined equals `xy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds typed val inside Ok((a,b)) match arm body")
# Regression for interpreter_val_in_ok_tuple_match_arm_not_visible_2026-06-04:
# typed val declared after the Ok((a,b)) pattern binding was not visible
# to subsequent statements in the same arm (exec_block_closure_mut dropped
# Pattern::Typed bindings; fixed 2026-06-12 via bind_pattern_value).
val res = Ok(("x", "y"))
match res:
    Ok((a, b)):
        val joined: text = a + b
        expect(joined).to_equal("xy")
    Err(_):
        assert_true(false)
```

</details>

#### binds multiple typed vals sequentially in Ok((a,b)) match arm

- binds multiple typed vals sequentially in Ok((a,b)) match arm
   - Expected: combined equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds multiple typed vals sequentially in Ok((a,b)) match arm")
val res = Ok(("hello", "world"))
match res:
    Ok((a, b)):
        val first: text = a
        val second: text = b
        val combined: text = first + " " + second
        expect(combined).to_equal("hello world")
    Err(_):
        assert_true(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/closure_nested_typed_binding_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering typed val bindings in nested closure blocks.
- typed val bindings in nested closure blocks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `e9ad576cec44a6c9defc38feef1ede4592cdf0970a529d98e14d5ec0f2476339`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e9ad576cec44a6c9defc38feef1ede4592cdf0970a529d98e14d5ec0f2476339`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e9ad576cec44a6c9defc38feef1ede4592cdf0970a529d98e14d5ec0f2476339`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/interpreter/closure_nested_typed_binding_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/closure_nested_typed_binding_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/closure_nested_typed_binding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/closure_nested_typed_binding_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/closure_nested_typed_binding_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/closure_nested_typed_binding_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds annotated i32 inside if and reads it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/closure_nested_typed_binding_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds annotated u32 inside if and passes it as call arg' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/closure_nested_typed_binding_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds annotated val inside while body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
