# World Units Newunit Specification

> Tests covering World units and newunit, REQ-WUN-001: nominal wrappers, REQ-WUN-004: exact derived units, REQ-WUN-006: currency identity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# World Units Newunit Specification

## Scenarios

### World units and newunit

### REQ-WUN-001: nominal wrappers

#### a newunit declaration is recorded as a nominal 1:1 wrapper

- register a newunit declaration the way the parser does
- rebuild the compile-start registry and look the wrapper up
   - Expected: entry.short_symbol equals `wuid`
   - Expected: entry.full_symbol equals `WunUserId`
   - Expected: entry.kind equals `i64`
   - Expected: entry.klass equals `UnitClass.Count`
   - Expected: entry.base_factor.numerator equals `1`
   - Expected: entry.base_factor.denominator equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-WUN-001
step("register a newunit declaration the way the parser does")
step("rebuild the compile-start registry and look the wrapper up")
val idx = newunit_register("WunUserId", "wuid", TYPE_I64)
assert_true(idx >= 0)
val reg = unit_registry_build()
match reg.lookup_entry("wuid"):
    case Some(entry):
        expect(entry.short_symbol).to_equal("wuid")
        expect(entry.full_symbol).to_equal("WunUserId")
        expect(entry.kind).to_equal("i64")
        expect(entry.klass).to_equal(UnitClass.Count)
        # nominal wrappers carry an identity base factor (1/1)
        expect(entry.base_factor.numerator).to_equal(1)
        expect(entry.base_factor.denominator).to_equal(1)
    case None:
        assert_true(false)
```

</details>

### REQ-WUN-004: exact derived units

#### km/h converts to m/s through the exact 5/18 factor

- register m, s, scaled km and h, and the km/h composite
- convert 18 km/h to m/s through the registry
   - Expected: value equals `5.0`
   - Expected: msg equals `unexpected conversion failure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-WUN-004
step("register m, s, scaled km and h, and the km/h composite")
step("convert 18 km/h to m/s through the registry")
val reg = UnitRegistry.new()
reg.register_unit("wunm", unit_expression_from_base("wunm"))
reg.register_unit("wuns", unit_expression_from_base("wuns"))
val km = unit_expression_scaled(exact_ratio(1000, 1), "wunm")
val h = unit_expression_scaled(exact_ratio(3600, 1), "wuns")
reg.register_unit("wunkm", km)
reg.register_unit("wunh", h)
reg.register_composite("wunkmph", unit_expression_div(km, h))
reg.register_composite("wunmps", unit_expression_div(
    unit_expression_from_base("wunm"), unit_expression_from_base("wuns")))
match reg.convert(18.0, "wunkmph", "wunmps"):
    case Ok(value):
        # oracle: 18 km/h = 18 * 1000/3600 m/s = 5 m/s exactly
        expect(value).to_equal(5.0)
    case Err(msg):
        expect(msg).to_equal("unexpected conversion failure")
```

</details>

### REQ-WUN-006: currency identity

#### a currency unit keeps its ISO code as its short symbol

- register USD as a Currency-class unit
- look it up by ISO code and check its class
   - Expected: entry.short_symbol equals `USD`
   - Expected: entry.klass equals `UnitClass.Currency`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-WUN-006
step("register USD as a Currency-class unit")
step("look it up by ISO code and check its class")
val reg = UnitRegistry.new()
reg.register_unit("USD", unit_expression_from_base("USD"))
reg.by_short["USD"].klass = UnitClass.Currency
match reg.lookup_entry("USD"):
    case Some(entry):
        expect(entry.short_symbol).to_equal("USD")
        expect(entry.klass).to_equal(UnitClass.Currency)
    case None:
        assert_true(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/world_units_newunit_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering World units and newunit, REQ-WUN-001: nominal wrappers, REQ-WUN-004: exact derived units, REQ-WUN-006: currency identity.
- World units and newunit
- REQ-WUN-001: nominal wrappers
- REQ-WUN-004: exact derived units
- REQ-WUN-006: currency identity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WUN-001`
- `REQ-WUN-004`
- `REQ-WUN-006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `438d22d511bb0bfb5a5814560e56f8e97d5a3ad44c21560541be9745730f5615`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `438d22d511bb0bfb5a5814560e56f8e97d5a3ad44c21560541be9745730f5615`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `438d22d511bb0bfb5a5814560e56f8e97d5a3ad44c21560541be9745730f5615`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/03_system/app/compiler/feature/world_units_newunit_spec.spl
mirror: doc/06_spec/03_system/app/compiler/feature/world_units_newunit_spec.md (current)
findings: 7 blockers: 0
  narrative=80 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/compiler/feature/world_units_newunit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/compiler/feature/world_units_newunit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/compiler/feature/world_units_newunit_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/03_system/app/compiler/feature/world_units_newunit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/compiler/feature/world_units_newunit_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a newunit declaration is recorded as a nominal 1:1 wrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/compiler/feature/world_units_newunit_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'km/h converts to m/s through the exact 5/18 factor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/compiler/feature/world_units_newunit_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a currency unit keeps its ISO code as its short symbol' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
