# Enum-Field Method Call Regression

> Regression test for Bug A from `doc/08_tracking/bug/memory_capabilities_interpreter_crashes_2026-06-11.md`: a method call on an enum value retrieved from a struct field crashed/failed because `interpreter_method/mod.rs` only consulted the local `enums` map when looking up enum body methods, never `GLOBAL_ENUMS`.  When the enum's definition was registered only in `GLOBAL_ENUMS` (cross-module or block-scoped), the lookup silently fell through and the interpreter produced a "method not found" error (or crash).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enum-Field Method Call Regression

Regression test for Bug A from `doc/08_tracking/bug/memory_capabilities_interpreter_crashes_2026-06-11.md`: a method call on an enum value retrieved from a struct field crashed/failed because `interpreter_method/mod.rs` only consulted the local `enums` map when looking up enum body methods, never `GLOBAL_ENUMS`.  When the enum's definition was registered only in `GLOBAL_ENUMS` (cross-module or block-scoped), the lookup silently fell through and the interpreter produced a "method not found" error (or crash).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTERP-ENUM-FIELD-METHOD |
| Category | Interpreter |
| Difficulty | 2/5 |
| Status | Regression |
| Source | `test/01_unit/compiler/interpreter/enum_field_method_call_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Regression test for Bug A from
`doc/08_tracking/bug/memory_capabilities_interpreter_crashes_2026-06-11.md`:
a method call on an enum value retrieved from a struct field crashed/failed
because `interpreter_method/mod.rs` only consulted the local `enums` map when
looking up enum body methods, never `GLOBAL_ENUMS`.  When the enum's definition
was registered only in `GLOBAL_ENUMS` (cross-module or block-scoped), the
lookup silently fell through and the interpreter produced a "method not found"
error (or crash).

The fix adds a `GLOBAL_ENUMS` fallback probe in the `Value::Enum` method
dispatch path, mirroring the three-tier lookup used in
`interpreter_call/mod.rs` and `interpreter/expr/calls.rs`.

These tests exercise:
1. Plain enum-on-its-own method call (baseline).
2. Enum value stored in a struct field — method called on the retrieved value.
3. Nested: struct field holds an enum; inner method returns a string; checked
   with `.to_equal()`.

## Scenarios

### enum-field method call — interpreter regression

#### calls a method on a standalone enum value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- calls a method on a standalone enum value
   - Expected: name equals `read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls a method on a standalone enum value")
val k = CapKind.Read
val name = k.label()
expect(name).to_equal("read")
```

</details>

#### calls a method on an enum value stored in a struct field

- calls a method on an enum value stored in a struct field
   - Expected: name equals `write`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls a method on an enum value stored in a struct field")
val entry = CapEntry(kind: CapKind.Write)
val k = entry.kind
val name = k.label()
expect(name).to_equal("write")
```

</details>

#### calls a method via temp var after field access

- calls a method via temp var after field access
   - Expected: k.label() equals `exec`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls a method via temp var after field access")
val entry = CapEntry(kind: CapKind.Exec)
val k = entry.kind
expect(k.label()).to_equal("exec")
```

</details>

#### round-trips all three variants via struct field

- round-trips all three variants via struct field
   - Expected: rk.label() equals `read`
   - Expected: wk.label() equals `write`
   - Expected: ek.label() equals `exec`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips all three variants via struct field")
val r = CapEntry(kind: CapKind.Read)
val w = CapEntry(kind: CapKind.Write)
val e = CapEntry(kind: CapKind.Exec)
val rk = r.kind
val wk = w.kind
val ek = e.kind
expect(rk.label()).to_equal("read")
expect(wk.label()).to_equal("write")
expect(ek.label()).to_equal("exec")
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8ad32ec97fbe745680a46345bf9adb66fe36479e8711e9604614355b9c1ec7d3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8ad32ec97fbe745680a46345bf9adb66fe36479e8711e9604614355b9c1ec7d3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8ad32ec97fbe745680a46345bf9adb66fe36479e8711e9604614355b9c1ec7d3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/interpreter/enum_field_method_call_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/enum_field_method_call_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/enum_field_method_call_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/enum_field_method_call_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/enum_field_method_call_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls a method on a standalone enum value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/enum_field_method_call_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls a method on an enum value stored in a struct field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/enum_field_method_call_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls a method via temp var after field access' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
