# Units Newunit Registry Specification

> Tests covering newunit registry collection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Units Newunit Registry Specification

## Scenarios

### newunit registry collection

#### records a newunit declaration in the parser-side registry

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records a newunit declaration in the parser-side registry


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records a newunit declaration in the parser-side registry")
val idx = newunit_register("SpecUserId", "suid", TYPE_I64)
assert_true(idx >= 0)
assert_true(newunit_count() > idx)
```

</details>

#### unit_registry_build makes a recorded newunit visible by suffix

- unit_registry_build makes a recorded newunit visible by suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unit_registry_build makes a recorded newunit visible by suffix")
newunit_register("SpecMeters", "smtr", TYPE_I64)
val reg = unit_registry_build()
assert_true(reg.has("smtr"))
```

</details>

#### collected entry carries name, suffix, and underlying kind

- collected entry carries name, suffix, and underlying kind
   - Expected: entry.short_symbol equals `sprc`
   - Expected: entry.full_symbol equals `SpecPrice`
   - Expected: entry.kind equals `f64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collected entry carries name, suffix, and underlying kind")
newunit_register("SpecPrice", "sprc", TYPE_F64)
val reg = unit_registry_build()
match reg.lookup_entry("sprc"):
    case Some(entry):
        expect(entry.short_symbol).to_equal("sprc")
        expect(entry.full_symbol).to_equal("SpecPrice")
        expect(entry.kind).to_equal("f64")
    case None:
        assert_true(false)
```

</details>

#### entry is also visible by full type name

- entry is also visible by full type name
   - Expected: entry.short_symbol equals `swt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("entry is also visible by full type name")
newunit_register("SpecWeight", "swt", TYPE_I64)
val reg = unit_registry_build()
match reg.lookup_entry("SpecWeight"):
    case Some(entry):
        expect(entry.short_symbol).to_equal("swt")
    case None:
        assert_true(false)
```

</details>

#### re-registering the same name updates instead of duplicating

- re-registering the same name updates instead of duplicating
   - Expected: a equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-registering the same name updates instead of duplicating")
val a = newunit_register("SpecDup", "sd1", TYPE_I64)
val b = newunit_register("SpecDup", "sd2", TYPE_I64)
expect(a).to_equal(b)
val reg = UnitRegistry.new()
unit_registry_collect_newunits(reg)
assert_true(reg.has("sd2"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/types/units_newunit_registry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering newunit registry collection.
- newunit registry collection

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d295d2d537674e6b1b7f57a315211c42eb6af001e02de487e22a0b2a9901c8a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d295d2d537674e6b1b7f57a315211c42eb6af001e02de487e22a0b2a9901c8a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d295d2d537674e6b1b7f57a315211c42eb6af001e02de487e22a0b2a9901c8a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/types/units_newunit_registry_spec.spl
mirror: doc/06_spec/01_unit/compiler/types/units_newunit_registry_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/types/units_newunit_registry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/types/units_newunit_registry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/types/units_newunit_registry_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records a newunit declaration in the parser-side registry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/types/units_newunit_registry_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unit_registry_build makes a recorded newunit visible by suffix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/types/units_newunit_registry_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collected entry carries name, suffix, and underlying kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
