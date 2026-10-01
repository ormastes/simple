# Option Returning Method Not Scalar Aliased Specification

> Tests covering no Option-returning method is aliased to a scalar-returning runtime symbol.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Option Returning Method Not Scalar Aliased Specification

## Scenarios

### no Option-returning method is aliased to a scalar-returning runtime symbol

#### reads every emitter that carries a copy of the alias table

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads every emitter that carries a copy of the alias table
- The invariant is only meaningful if the sources were actually read -- an unreadable path would make every absence check below vacuously true
- Each emitter must actually contain an alias table mentioning the string conversions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads every emitter that carries a copy of the alias table")
step("The invariant is only meaningful if the sources were actually read -- an unreadable path would make every absence check below vacuously true")
for path in EMITTERS:
    val body = source_of(path)
    assert_true(body.len() > 0)
    step("Each emitter must actually contain an alias table mentioning the string conversions")
    assert_true(body.contains("rt_string_to_int"))
```

</details>

#### never maps a parse_* method onto the bare-i64 rt_string_to_int

- never maps a parse_* method onto the bare-i64 rt_string_to_int
- `rt_string_to_int` returns a bare `i64` and answers 0 for both "0" and "abc", so it cannot represent None. This is the exact pairing that produced the bug


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("never maps a parse_* method onto the bare-i64 rt_string_to_int")
step("`rt_string_to_int` returns a bare `i64` and answers 0 for both \"0\" and \"abc\", so it cannot represent None. This is the exact pairing that produced the bug")
for path in EMITTERS:
    val body = source_of(path)
    assert_equal(lines_with_both(body, "parse_int", "rt_string_to_int"), 0)
    assert_equal(lines_with_both(body, "parse_i64", "rt_string_to_int"), 0)
    assert_equal(lines_with_both(body, "parse_i32", "rt_string_to_int"), 0)
```

</details>

#### routes every int parse spelling to the Option-shaped rt_string_parse_int

- routes every int parse spelling to the Option-shaped rt_string_parse_int
- All five emitters must be fixed, not four: a partial fix is this class's most likely recurrence, and no single-lane behavioural test would see it
- All three spellings the interpreter accepts must be routed, or the unrouted one dies with `Function 'str.parse_i64' not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("routes every int parse spelling to the Option-shaped rt_string_parse_int")
step("All five emitters must be fixed, not four: a partial fix is this class's most likely recurrence, and no single-lane behavioural test would see it")
for path in EMITTERS:
    val body = source_of(path)
    assert_true(body.contains("rt_string_parse_int"))
    step("All three spellings the interpreter accepts must be routed, or the unrouted one dies with `Function 'str.parse_i64' not found`")
    assert_true(lines_with_both(body, "parse_int", "rt_string_parse_int") > 0)
    assert_true(lines_with_both(body, "parse_i64", "rt_string_parse_int") > 0)
    assert_true(lines_with_both(body, "parse_i32", "rt_string_parse_int") > 0)
```

</details>

#### keeps the TOTAL conversions on their bare-scalar symbols

- keeps the TOTAL conversions on their bare-scalar symbols
- The inverse failure mode: making every conversion an Option would break each caller of the total ones. `to_int`/`to_i64` are specified to yield 0 on failure, so they must stay on rt_string_to_int


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the TOTAL conversions on their bare-scalar symbols")
step("The inverse failure mode: making every conversion an Option would break each caller of the total ones. `to_int`/`to_i64` are specified to yield 0 on failure, so they must stay on rt_string_to_int")
for path in EMITTERS:
    val body = source_of(path)
    assert_true(lines_with_both(body, "to_int", "rt_string_to_int") > 0)
    assert_equal(lines_with_both(body, "to_int", "rt_string_parse_int"), 0)
    assert_equal(lines_with_both(body, "to_i64", "rt_string_parse_int"), 0)
```

</details>

#### types the parse family as a tagged value and the total family as i64 in HIR

- types the parse family as a tagged value and the total family as i64 in HIR
- The name->symbol table is only half the defect. HIR typed `parse_int` as TypeId::I64, which is what erased the Option at the type level -- so the HIR table has to agree with the emitters
- The parse family must NOT be typed I64 on the same arm as the total conversions
- It must be ANY -- the tagged/erased slot the already-correct parse_f64 family uses
- And the total conversions must still be I64


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("types the parse family as a tagged value and the total family as i64 in HIR")
step("The name->symbol table is only half the defect. HIR typed `parse_int` as TypeId::I64, which is what erased the Option at the type level -- so the HIR table has to agree with the emitters")
val hir = source_of("src/compiler_rust/compiler/src/hir/lower/expr/mod.rs")
assert_true(hir.len() > 0)

step("The parse family must NOT be typed I64 on the same arm as the total conversions")
assert_equal(lines_with_both(hir, "\"parse_int\"", "TypeId::I64"), 0)
assert_equal(lines_with_both(hir, "\"parse_i64\"", "TypeId::I64"), 0)

step("It must be ANY -- the tagged/erased slot the already-correct parse_f64 family uses")
assert_true(lines_with_both(hir, "\"parse_int\"", "TypeId::ANY") > 0)

step("And the total conversions must still be I64")
assert_true(lines_with_both(hir, "\"to_int\"", "TypeId::I64") > 0)
```

</details>

#### backs the Option-shaped symbol with a real runtime definition

- backs the Option-shaped symbol with a real runtime definition
- A routed symbol with no definition trades a silent wrong answer for an unresolved-symbol failure -- better, but still broken
- It must return a RuntimeValue, not an i64 -- returning a scalar under an Option-shaped name would reintroduce the defect behind a correct-looking name
- And it must be exported, or the JIT cannot resolve it at all


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("backs the Option-shaped symbol with a real runtime definition")
step("A routed symbol with no definition trades a silent wrong answer for an unresolved-symbol failure -- better, but still broken")
val rt = source_of("src/compiler_rust/runtime/src/value/collections.rs")
assert_true(rt.len() > 0)
assert_true(rt.contains("pub extern \"C\" fn rt_string_parse_int"))

step("It must return a RuntimeValue, not an i64 -- returning a scalar under an Option-shaped name would reintroduce the defect behind a correct-looking name")
assert_true(lines_with_both(rt, "fn rt_string_parse_int", "-> RuntimeValue") > 0)

step("And it must be exported, or the JIT cannot resolve it at all")
val exports = source_of("src/compiler_rust/runtime/src/value/mod.rs")
assert_true(exports.len() > 0)
assert_true(exports.contains("rt_string_parse_int"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/option_returning_method_not_scalar_aliased_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering no Option-returning method is aliased to a scalar-returning runtime symbol.
- no Option-returning method is aliased to a scalar-returning runtime symbol

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `b5ad9c535a1d2e3cd48f827da27a5b8b7f6bb0ab57793026828909fb77299ae8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b5ad9c535a1d2e3cd48f827da27a5b8b7f6bb0ab57793026828909fb77299ae8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b5ad9c535a1d2e3cd48f827da27a5b8b7f6bb0ab57793026828909fb77299ae8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/option_returning_method_not_scalar_aliased_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/option_returning_method_not_scalar_aliased_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/option_returning_method_not_scalar_aliased_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/option_returning_method_not_scalar_aliased_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/option_returning_method_not_scalar_aliased_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads every emitter that carries a copy of the alias table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/option_returning_method_not_scalar_aliased_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never maps a parse_* method onto the bare-i64 rt_string_to_int' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/option_returning_method_not_scalar_aliased_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes every int parse spelling to the Option-shaped rt_string_parse_int' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
