# Enum Discriminant Shift-by-63 Specification

> `eval_enum_discriminant_expr` (src/compiler/10.frontend/core/enum_discriminant_eval.spl) evaluates constant enum-discriminant expressions, including shift operators. Shift amounts are bounds-checked against the 64-bit width of `i64`. The largest valid shift amount for a 64-bit value is 63 (shifting by 64 or more is undefined), so `x >> 63` must be ACCEPTED as a valid constant expression, not rejected as an "invalid shift".

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enum Discriminant Shift-by-63 Specification

`eval_enum_discriminant_expr` (src/compiler/10.frontend/core/enum_discriminant_eval.spl) evaluates constant enum-discriminant expressions, including shift operators. Shift amounts are bounds-checked against the 64-bit width of `i64`. The largest valid shift amount for a 64-bit value is 63 (shifting by 64 or more is undefined), so `x >> 63` must be ACCEPTED as a valid constant expression, not rejected as an "invalid shift".

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler \| Frontend \| Enum discriminants |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/compiler/frontend/enum_discriminant_shift63_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`eval_enum_discriminant_expr` (src/compiler/10.frontend/core/enum_discriminant_eval.spl)
evaluates constant enum-discriminant expressions, including shift operators.
Shift amounts are bounds-checked against the 64-bit width of `i64`. The
largest valid shift amount for a 64-bit value is 63 (shifting by 64 or more
is undefined), so `x >> 63` must be ACCEPTED as a valid constant expression,
not rejected as an "invalid shift".

This spec parses a real enum declaration through the self-hosted parser
(`parse_and_build_module`) and calls `eval_enum_discriminant_expr` directly
on the resulting discriminant expression id, so it exercises the real
arena-backed AST rather than a hand-rolled fixture.

## Scenarios

### eval_enum_discriminant_expr — shift amount of exactly 63

#### accepts `9223372036854775807 >> 63` and evaluates it to 0

- accepts `9223372036854775807 >> 63` and evaluates it to 0
   - Expected: decl >= 0 is true
   - Expected: defaults.len() equals `1`
   - Expected: result.valid is true
   - Expected: result.value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts `9223372036854775807 >> 63` and evaluates it to 0")
val source = "enum ShiftBy63:\n    Zero = 9223372036854775807 >> 63\n"
val module = parse_and_build_module(source, "shift63.spl")
val decl = find_decl_by_name("ShiftBy63")
expect(decl >= 0).to_equal(true)

val defaults = decl_get_field_defaults(decl)
expect(defaults.len()).to_equal(1)

val result = eval_enum_discriminant_expr(defaults[0], "ShiftBy63", [], [])
expect(result.valid).to_equal(true)
expect(result.value).to_equal(0)
```

</details>

#### still rejects an out-of-range shift amount of 64

- still rejects an out-of-range shift amount of 64
   - Expected: decl >= 0 is true
   - Expected: defaults.len() equals `1`
   - Expected: result.valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still rejects an out-of-range shift amount of 64")
val source = "enum ShiftBy64:\n    Zero = 1 >> 64\n"
val module = parse_and_build_module(source, "shift64.spl")
val decl = find_decl_by_name("ShiftBy64")
expect(decl >= 0).to_equal(true)

val defaults = decl_get_field_defaults(decl)
expect(defaults.len()).to_equal(1)

val result = eval_enum_discriminant_expr(defaults[0], "ShiftBy64", [], [])
expect(result.valid).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `21cb3223b96665d480e5dbc1808b23a9b25579c04953ca7669971e4095b42d97`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `21cb3223b96665d480e5dbc1808b23a9b25579c04953ca7669971e4095b42d97`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `21cb3223b96665d480e5dbc1808b23a9b25579c04953ca7669971e4095b42d97`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/frontend/enum_discriminant_shift63_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/enum_discriminant_shift63_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/enum_discriminant_shift63_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/enum_discriminant_shift63_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/enum_discriminant_shift63_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/frontend/enum_discriminant_shift63_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts `9223372036854775807 >> 63` and evaluates it to 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/enum_discriminant_shift63_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still rejects an out-of-range shift amount of 64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
