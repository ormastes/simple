# Value Specification

> Tests covering Value.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Value Specification

## Scenarios

### Value

#### keeps interpreter value kind constants and constructors available

- keeps interpreter value kind constants and constructors available


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("keeps interpreter value kind constants and constructors available")
val source = interpreter_value_source()

expect(source).to_contain("val VAL_NIL: i64 = 0")
expect(source).to_contain("val VAL_BOOL: i64 = 1")
expect(source).to_contain("val VAL_INT: i64 = 2")
expect(source).to_contain("val VAL_TEXT: i64 = 4")
expect(source).to_contain("fn val_make_nil() -> i64")
expect(source).to_contain("fn val_make_bool(b: bool) -> i64")
expect(source).to_contain("fn val_make_int(n: i64) -> i64")
expect(source).to_contain("fn val_make_text(s: text) -> i64")
```

</details>

#### keeps interpreter value accessors and predicates available

- keeps interpreter value accessors and predicates available


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("keeps interpreter value accessors and predicates available")
val source = interpreter_value_source()

expect(source).to_contain("fn val_get_kind(vid: i64) -> i64")
expect(source).to_contain("fn val_get_int(vid: i64) -> i64")
expect(source).to_contain("fn val_get_bool(vid: i64) -> bool")
expect(source).to_contain("fn val_get_text(vid: i64) -> text")
expect(source).to_contain("fn val_is_truthy(vid: i64) -> bool")
expect(source).to_contain("fn val_to_text(vid: i64) -> text")
expect(source).to_contain("fn val_equals(a: i64, b: i64) -> bool")
```

</details>

#### uses the canonical value-kind accessor in type checking

- uses the canonical value-kind accessor in type checking
   - Expected: source does not contain `val_kind(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("uses the canonical value-kind accessor in type checking")
val source = value_kind_consumers_source()

expect(source).to_contain("extern fn val_get_kind(value_id: i64) -> i64")
expect(source.contains("val_kind(")).to_equal(false)
```

</details>

#### keeps struct and thunk value support available

- keeps struct and thunk value support available


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("keeps struct and thunk value support available")
val source = interpreter_value_source()

expect(source).to_contain("fn val_make_struct(type_name: text, field_names: [text], field_values: [i64]) -> i64")
expect(source).to_contain("fn val_struct_get_field(vid: i64, field_name: text) -> i64")
expect(source).to_contain("fn val_struct_set_field(vid: i64, field_name: text, new_val: i64)")
expect(source).to_contain("fn val_make_thunk(expr_id: i64) -> i64")
expect(source).to_contain("fn val_is_thunk(vid: i64) -> bool")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/interpreter/value_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Value.
- Value

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
- `REQ-SSPEC-COMPILER_CORE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `97181aed9ba52d97c5a0dad2663ebd47863fc7be9c7f74a0f174074dedac2c61`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `97181aed9ba52d97c5a0dad2663ebd47863fc7be9c7f74a0f174074dedac2c61`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `97181aed9ba52d97c5a0dad2663ebd47863fc7be9c7f74a0f174074dedac2c61`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler_core/interpreter/value_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/interpreter/value_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler_core/interpreter/value_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/interpreter/value_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/interpreter/value_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler_core/interpreter/value_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler_core/interpreter/value_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps interpreter value kind constants and constructors available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/interpreter/value_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps interpreter value accessors and predicates available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/interpreter/value_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the canonical value-kind accessor in type checking' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
