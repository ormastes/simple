# world_units_spec

> Purpose: Prove that World unit model.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# world_units_spec

Purpose: Prove that World unit model.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/units/world_units_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that World unit model.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### World unit model

#### keeps km/h conversion exact

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps km/h conversion exact
- Verify: keeps km/h conversion exact
   - Expected: factor.numerator equals `5`
   - Expected: factor.denominator equals `18`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps km/h conversion exact")
step("Verify: keeps km/h conversion exact")
# @req: REQ-LIB-COMMON-001
val factor = kilometre_per_hour_factor_to_metre_per_second()
expect(factor.numerator).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(factor.denominator).to_equal(18)  # oracle: 18 — named expected value from the requirement
```

</details>

#### blocks prefixes for accepted non-SI time and calendar units

- blocks prefixes for accepted non-SI time and calendar units
- Verify: blocks prefixes for accepted non-SI time and calendar units
   - Expected: is_prefix_blocked("h") is true
   - Expected: is_prefix_blocked("d") is true
   - Expected: is_prefix_blocked("a_g") is true
   - Expected: is_prefix_blocked("m") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("blocks prefixes for accepted non-SI time and calendar units")
step("Verify: blocks prefixes for accepted non-SI time and calendar units")
expect(is_prefix_blocked("h")).to_equal(true)
expect(is_prefix_blocked("d")).to_equal(true)
expect(is_prefix_blocked("a_g")).to_equal(true)
expect(is_prefix_blocked("m")).to_equal(false)
```

</details>

#### constructs exact ratios

- constructs exact ratios
- Verify: constructs exact ratios
   - Expected: ratio.numerator equals `1024`
   - Expected: ratio.denominator equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("constructs exact ratios")
step("Verify: constructs exact ratios")
val ratio = exact_ratio(1024, 1)
expect(ratio.numerator).to_equal(1024)  # oracle: 1024 — named expected value from the requirement
expect(ratio.denominator).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### normalizes exact ratios

- normalizes exact ratios
- Verify: normalizes exact ratios
   - Expected: ratio.numerator equals `-1`
   - Expected: ratio.denominator equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("normalizes exact ratios")
step("Verify: normalizes exact ratios")
val ratio = exact_ratio_normalize(exact_ratio(10, -20))
expect(ratio.numerator).to_equal(-1)  # oracle: -1 — named expected value from the requirement
expect(ratio.denominator).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### multiplies and divides exact ratios

- multiplies and divides exact ratios
- Verify: multiplies and divides exact ratios
   - Expected: multiplied.numerator equals `3`
   - Expected: multiplied.denominator equals `2`
   - Expected: divided.numerator equals `1`
   - Expected: divided.denominator equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("multiplies and divides exact ratios")
step("Verify: multiplies and divides exact ratios")
val multiplied = exact_ratio_mul(exact_ratio(2, 3), exact_ratio(9, 4))
val divided = exact_ratio_div(exact_ratio(5, 18), exact_ratio(10, 3))
expect(multiplied.numerator).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(multiplied.denominator).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(divided.numerator).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(divided.denominator).to_equal(12)  # oracle: 12 — named expected value from the requirement
```

</details>

#### normalizes derived unit expressions exactly

- normalizes derived unit expressions exactly
- Verify: normalizes derived unit expressions exactly
   - Expected: expression.scale.numerator equals `5`
   - Expected: expression.scale.denominator equals `18`
   - Expected: unit_expression_factor_exponent(expression, "metre") equals `1`
   - Expected: unit_expression_factor_exponent(expression, "second") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("normalizes derived unit expressions exactly")
step("Verify: normalizes derived unit expressions exactly")
val expression = kilometre_per_hour_expression()
expect(expression.scale.numerator).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(expression.scale.denominator).to_equal(18)  # oracle: 18 — named expected value from the requirement
expect(unit_expression_factor_exponent(expression, "metre")).to_equal(1)
expect(unit_expression_factor_exponent(expression, "second")).to_equal(-1)
```

</details>

#### cancels matching unit factors

- cancels matching unit factors
- Verify: cancels matching unit factors
   - Expected: unit_expression_factor_count(expression) equals `1`
   - Expected: unit_expression_factor_exponent(expression, "second") equals `1`
   - Expected: unit_expression_factor_exponent(expression, "metre") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("cancels matching unit factors")
step("Verify: cancels matching unit factors")
val expression = unit_expression_div(
    unit_expression_mul(unit_expression_from_base("metre"), unit_expression_from_base("second")),
    unit_expression_from_base("metre")
)
expect(unit_expression_factor_count(expression)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(unit_expression_factor_exponent(expression, "second")).to_equal(1)
expect(unit_expression_factor_exponent(expression, "metre")).to_equal(0)
```

</details>

#### represents amount concentration through litre composition

- represents amount concentration through litre composition
- Verify: represents amount concentration through litre composition
   - Expected: expression.scale.numerator equals `1000`
   - Expected: expression.scale.denominator equals `1`
   - Expected: unit_expression_factor_exponent(expression, "mole") equals `1`
   - Expected: unit_expression_factor_exponent(expression, "metre") equals `-3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("represents amount concentration through litre composition")
step("Verify: represents amount concentration through litre composition")
val expression = mole_per_litre_expression()
expect(expression.scale.numerator).to_equal(1000)  # oracle: 1000 — named expected value from the requirement
expect(expression.scale.denominator).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(unit_expression_factor_exponent(expression, "mole")).to_equal(1)
expect(unit_expression_factor_exponent(expression, "metre")).to_equal(-3)
```

</details>

#### pins required catalog identities

- pins required catalog identities
- Verify: pins required catalog identities
   - Expected: catalog_has_required_world_units(catalog) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pins required catalog identities")
step("Verify: pins required catalog identities")
val catalog = file_read("src/lib/common/units/catalog/world_units_v1.sdn")
expect(catalog_has_required_world_units(catalog)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bdffbbb896bcd4d42a60ed6161c8ba81c376818ba1dc79a93ab451d0b41664fd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bdffbbb896bcd4d42a60ed6161c8ba81c376818ba1dc79a93ab451d0b41664fd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bdffbbb896bcd4d42a60ed6161c8ba81c376818ba1dc79a93ab451d0b41664fd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/units/world_units_spec.spl
mirror: doc/06_spec/01_unit/lib/common/units/world_units_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/units/world_units_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/units/world_units_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/units/world_units_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/units/world_units_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps km/h conversion exact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/units/world_units_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks prefixes for accepted non-SI time and calendar units' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/units/world_units_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs exact ratios' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
