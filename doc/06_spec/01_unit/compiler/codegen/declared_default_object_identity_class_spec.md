# Declared Default Object Identity Class Specification

> Tests covering declared field defaults are real values on every engine.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Declared Default Object Identity Class Specification

## Scenarios

### declared field defaults are real values on every engine

#### holds on the interpreter (control arm)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- holds on the interpreter (control arm)
- Run the probe under SIMPLE_EXECUTION_MODE=interpreter
- The interpreter was measured correct on all 18 checks 2026-08-17; a red here means the probe is broken, not the engine


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("holds on the interpreter (control arm)")
step("Run the probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The interpreter was measured correct on all 18 checks 2026-08-17; a red here means the probe is broken, not the engine")
expect(interp).to_contain("DECLARED_DEFAULT_OBJECT_IDENTITY PROBE: ALL PASS")
```

</details>

#### holds for scalar defaults under the cranelift JIT

- holds for scalar defaults under the cranelift JIT
- Run the same probe under SIMPLE_EXECUTION_MODE=jit
- bool / i64 / f64 / str defaults must read back as themselves, not as the nil tag 3, 0, or a len -1 string
- The same on a class, whose construction takes a different lowering path than a struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("holds for scalar defaults under the cranelift JIT")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit")
val jit = run_probe_in_mode("jit")

step("bool / i64 / f64 / str defaults must read back as themselves, not as the nil tag 3, 0, or a len -1 string")
expect(jit).to_contain("PASS default_bool_reads_true")
expect(jit).to_contain("PASS default_i64_reads_7")
expect(jit).to_contain("PASS default_f64_reads_1_5")
expect(jit).to_contain("PASS default_str_len_1")

step("The same on a class, whose construction takes a different lowering path than a struct")
expect(jit).to_contain("PASS class_default_i64")
```

</details>

#### holds for container defaults under the cranelift JIT

- holds for container defaults under the cranelift JIT
- An `[]` default must be a live array: push, element read, second push, and pop-shrink
- A `{}` default must accept an insert, report len 1, and read the value back
- The differential control arm — an explicitly assigned empty container — must also pass, or the defect is broader than construction-site defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("holds for container defaults under the cranelift JIT")
val jit = run_probe_in_mode("jit")

step("An `[]` default must be a live array: push, element read, second push, and pop-shrink")
expect(jit).to_contain("PASS default_array_accepts_push")
expect(jit).to_contain("PASS default_array_element_value")
expect(jit).to_contain("PASS default_array_second_push")
expect(jit).to_contain("PASS default_array_pop_shrinks")
expect(jit).to_contain("PASS default_str_array_accepts_push")

step("A `{}` default must accept an insert, report len 1, and read the value back")
expect(jit).to_contain("PASS default_dict_accepts_insert")
expect(jit).to_contain("PASS default_dict_value_readback")

step("The differential control arm — an explicitly assigned empty container — must also pass, or the defect is broader than construction-site defaults")
expect(jit).to_contain("PASS control_explicit_empty_then_push")
```

</details>

#### holds for nested-struct defaults under the cranelift JIT

- holds for nested-struct defaults under the cranelift JIT
- A `var inner: Inner = Inner()` default must carry Inner's own defaults, not zeros


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("holds for nested-struct defaults under the cranelift JIT")
val jit = run_probe_in_mode("jit")

step("A `var inner: Inner = Inner()` default must carry Inner's own defaults, not zeros")
expect(jit).to_contain("PASS default_nested_struct_field")
expect(jit).to_contain("PASS default_nested_struct_write")
```

</details>

#### reports no failing check at all under the cranelift JIT

- reports no failing check at all under the cranelift JIT
- The whole-probe verdict — this catches any future field type added to the probe without a matching assertion above


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports no failing check at all under the cranelift JIT")
val jit = run_probe_in_mode("jit")

step("The whole-probe verdict — this catches any future field type added to the probe without a matching assertion above")
expect(jit).to_contain("DECLARED_DEFAULT_OBJECT_IDENTITY PROBE: ALL PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/declared_default_object_identity_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering declared field defaults are real values on every engine.
- declared field defaults are real values on every engine

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b6515542bffc9ed75850ac3a109a0a8a3341b67823c2138a649753d39d58f8da`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b6515542bffc9ed75850ac3a109a0a8a3341b67823c2138a649753d39d58f8da`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b6515542bffc9ed75850ac3a109a0a8a3341b67823c2138a649753d39d58f8da`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/declared_default_object_identity_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/declared_default_object_identity_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/declared_default_object_identity_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/declared_default_object_identity_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/declared_default_object_identity_class_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'holds on the interpreter (control arm)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/declared_default_object_identity_class_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'holds for scalar defaults under the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/declared_default_object_identity_class_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'holds for container defaults under the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
