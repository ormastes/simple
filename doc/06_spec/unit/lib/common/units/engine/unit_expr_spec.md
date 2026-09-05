# unit_expr_spec

> Purpose: Prove that World unit expression engine.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# unit_expr_spec

Purpose: Prove that World unit expression engine.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/units/engine/unit_expr_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that World unit expression engine.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### World unit expression engine

#### parses km per hour exactly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses km per hour exactly
- Verify: parses km per hour exactly
   - Expected: parsed.ok is true
   - Expected: parsed.expression.scale.numerator equals `5`
   - Expected: parsed.expression.scale.denominator equals `18`
   - Expected: unit_expression_factor_exponent(parsed.expression, "metre") equals `1`
   - Expected: unit_expression_factor_exponent(parsed.expression, "second") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses km per hour exactly")
step("Verify: parses km per hour exactly")
# @req: REQ-LIB-COMMON-001
val parsed = parse_unit_expression("km/h")
expect(parsed.ok).to_equal(true)
expect(parsed.expression.scale.numerator).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(parsed.expression.scale.denominator).to_equal(18)  # oracle: 18 — named expected value from the requirement
expect(unit_expression_factor_exponent(parsed.expression, "metre")).to_equal(1)
expect(unit_expression_factor_exponent(parsed.expression, "second")).to_equal(-1)
```

</details>

#### accepts canonical aliases without changing canonical formatting

- accepts canonical aliases without changing canonical formatting
- Verify: accepts canonical aliases without changing canonical formatting
   - Expected: parsed.ok is true
   - Expected: format_unit_expression(parsed.expression) equals `km/h`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts canonical aliases without changing canonical formatting")
step("Verify: accepts canonical aliases without changing canonical formatting")
val parsed = parse_unit_expression("kmph")
expect(parsed.ok).to_equal(true)
expect(format_unit_expression(parsed.expression)).to_equal("km/h")
```

</details>

#### parses chemistry concentration aliases

- parses chemistry concentration aliases
- Verify: parses chemistry concentration aliases
   - Expected: parsed.ok is true
   - Expected: parsed.expression.scale.numerator equals `1000`
   - Expected: unit_expression_factor_exponent(parsed.expression, "mole") equals `1`
   - Expected: unit_expression_factor_exponent(parsed.expression, "metre") equals `-3`
   - Expected: format_unit_expression(parsed.expression) equals `mol/L`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses chemistry concentration aliases")
step("Verify: parses chemistry concentration aliases")
val parsed = parse_unit_expression("M")
expect(parsed.ok).to_equal(true)
expect(parsed.expression.scale.numerator).to_equal(1000)  # oracle: 1000 — named expected value from the requirement
expect(unit_expression_factor_exponent(parsed.expression, "mole")).to_equal(1)
expect(unit_expression_factor_exponent(parsed.expression, "metre")).to_equal(-3)
expect(format_unit_expression(parsed.expression)).to_equal("mol/L")
```

</details>

#### reports unsupported expressions

- reports unsupported expressions
- Verify: reports unsupported expressions
   - Expected: parsed.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports unsupported expressions")
step("Verify: reports unsupported expressions")
val parsed = parse_unit_expression("USD/h")
expect(parsed.ok).to_equal(false)
expect(parsed.error).to_contain("unknown unit expression")
```

</details>

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
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `723018138cbce05430f72fc57c99924010cff26a7739b69c765a061cf436f145`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `723018138cbce05430f72fc57c99924010cff26a7739b69c765a061cf436f145`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `723018138cbce05430f72fc57c99924010cff26a7739b69c765a061cf436f145`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/units/engine/unit_expr_spec.spl
mirror: doc/06_spec/unit/lib/common/units/engine/unit_expr_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/units/engine/unit_expr_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/units/engine/unit_expr_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/units/engine/unit_expr_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/units/engine/unit_expr_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses km per hour exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/units/engine/unit_expr_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts canonical aliases without changing canonical formatting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/units/engine/unit_expr_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses chemistry concentration aliases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
