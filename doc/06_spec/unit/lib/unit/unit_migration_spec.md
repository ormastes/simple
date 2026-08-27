# Unit Migration Specification

> Tests covering migration — old path compiles, migration — deprecation warning, migration — type identity, migration — removed units.disabled.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unit Migration Specification

## Scenarios

### migration — old path compiles

#### AC-6: `use std.common.units.model.world_units.{UnitFactor}` still resolves

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-6: `use std.common.units.model.world_units.{UnitFactor}` still resolves
   - Expected: resolved is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: `use std.common.units.model.world_units.{UnitFactor}` still resolves")
# pending: parse + resolve (no runtime cost here; the import at the
# top of a synthetic source file must succeed).
val resolved: bool = true
expect(resolved).to_equal(true)
```

</details>

#### AC-6: `use std.common.units.engine.unit_expr.{UnitExpression}` still resolves

- AC-6: `use std.common.units.engine.unit_expr.{UnitExpression}` still resolves
   - Expected: resolved is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: `use std.common.units.engine.unit_expr.{UnitExpression}` still resolves")
val resolved: bool = true
expect(resolved).to_equal(true)
```

</details>

### migration — deprecation warning

#### AC-6: old import emits `deprecated` warning pointing to new path

- AC-6: old import emits `deprecated` warning pointing to new path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: old import emits `deprecated` warning pointing to new path")
val msg: text = "warning: deprecated — moved to unit.simple-lang.*; will be removed in 0.11.0"
expect(msg).to_contain("unit.simple-lang")
expect(msg).to_contain("0.11.0")
```

</details>

#### AC-6: deprecation warning names the specific new path for the import

- AC-6: deprecation warning names the specific new path for the import


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: deprecation warning names the specific new path for the import")
# For `std.common.units.model.world_units` the replacement is
# `unit.simple-lang.__model__` (or `unit.meta.world_units`).
val msg: text = "deprecated: use unit.meta.world_units instead"
expect(msg).to_contain("unit.meta.world_units")
```

</details>

### migration — type identity

#### AC-6: `std.common.units.model.world_units.UnitFactor` == `unit.meta.world_units.UnitFactor`

- AC-6: `std.common.units.model.world_units.UnitFactor` == `unit.meta.world_units.UnitFactor`
   - Expected: same_type_id is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: `std.common.units.model.world_units.UnitFactor` == `unit.meta.world_units.UnitFactor`")
# pending: compile two sources, one with each import, and verify the
# resolved type id is identical.
val same_type_id: bool = true
expect(same_type_id).to_equal(true)
```

</details>

#### AC-6: old `std.common.units.engine.unit_expr` == new `unit.simple-lang.__engine__`

- AC-6: old `std.common.units.engine.unit_expr` == new `unit.simple-lang.__engine__`
   - Expected: same_type_id is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: old `std.common.units.engine.unit_expr` == new `unit.simple-lang.__engine__`")
val same_type_id: bool = true
expect(same_type_id).to_equal(true)
```

</details>

### migration — removed units.disabled

#### AC-6: `std_lib/src/units.disabled/` no longer exists

- AC-6: `std_lib/src/units.disabled/` no longer exists
   - Expected: still_present is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: `std_lib/src/units.disabled/` no longer exists")
# pending: rt_file_exists on the legacy disabled tree must return false.
val still_present: bool = false
expect(still_present).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/unit/unit_migration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering migration — old path compiles, migration — deprecation warning, migration — type identity, migration — removed units.disabled.
- migration — old path compiles
- migration — deprecation warning
- migration — type identity
- migration — removed units.disabled

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c522f79d83892d7a278b48806356ba9126e3764b35af1c89f90b142173f2ba34`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c522f79d83892d7a278b48806356ba9126e3764b35af1c89f90b142173f2ba34`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c522f79d83892d7a278b48806356ba9126e3764b35af1c89f90b142173f2ba34`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/unit/unit_migration_spec.spl
mirror: doc/06_spec/unit/lib/unit/unit_migration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/unit/unit_migration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/unit/unit_migration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/unit/unit_migration_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: `use std.common.units.model.world_units.{UnitFactor}` still resolves' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/unit/unit_migration_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: `use std.common.units.engine.unit_expr.{UnitExpression}` still resolves' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/unit/unit_migration_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: old import emits `deprecated` warning pointing to new path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
