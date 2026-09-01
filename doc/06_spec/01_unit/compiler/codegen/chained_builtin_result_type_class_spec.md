# Chained Builtin Result Type Class Specification

> Tests covering chained builtin method results keep their static type.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chained Builtin Result Type Class Specification

## Scenarios

### chained builtin method results keep their static type

#### resolves every chained builtin correctly on the interpreter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves every chained builtin correctly on the interpreter
- Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter
- The interpreter is the control arm -- it was already correct, so a red here means the probe is broken rather than the engine


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves every chained builtin correctly on the interpreter")
step("Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The interpreter is the control arm -- it was already correct, so a red here means the probe is broken rather than the engine")
expect(interp).to_contain("PASS chained_substring_to_int")
expect(interp).to_contain("CHAINED_BUILTIN_RESULT_TYPE PROBE: ALL PASS")
```

</details>

#### resolves the filed reproducer correctly on the cranelift JIT

- resolves the filed reproducer correctly on the cranelift JIT
- Run the same probe under SIMPLE_EXECUTION_MODE=jit -- the engine the bug lived in
- The exact filed expression: arg.substring(10).to_int() must be 800, not a heap pointer
- The typed-intermediate control must stay correct


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves the filed reproducer correctly on the cranelift JIT")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit -- the engine the bug lived in")
val jit = run_probe_in_mode("jit")

step("The exact filed expression: arg.substring(10).to_int() must be 800, not a heap pointer")
expect(jit).to_contain("PASS chained_substring_to_int")

step("The typed-intermediate control must stay correct")
expect(jit).to_contain("PASS via_typed_val_to_int")
```

</details>

#### resolves the whole chained-builtin class on the cranelift JIT

- resolves the whole chained-builtin class on the cranelift JIT
- Every text-returning builtin feeding an integer cast is the same defect shape
- A float cast off a chained receiver used to fcvt the string's pointer
- Text-in/text-out chains must stay text, not decay to a pointer
- Length and predicate builtins chained off a text-returning builtin
- The aggregate verdict line is the authoritative result


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves the whole chained-builtin class on the cranelift JIT")
val jit = run_probe_in_mode("jit")

step("Every text-returning builtin feeding an integer cast is the same defect shape")
expect(jit).to_contain("PASS chained_substring_to_i64")
expect(jit).to_contain("PASS chained_substring_to_i32")
expect(jit).to_contain("PASS chained_trim_to_int")
expect(jit).to_contain("PASS chained_slice_to_int")
expect(jit).to_contain("PASS chained_replace_to_int")

step("A float cast off a chained receiver used to fcvt the string's pointer")
expect(jit).to_contain("PASS chained_substring_to_float")

step("Text-in/text-out chains must stay text, not decay to a pointer")
expect(jit).to_contain("PASS chained_substring_to_upper")
expect(jit).to_contain("PASS chained_trim_substring")

step("Length and predicate builtins chained off a text-returning builtin")
expect(jit).to_contain("PASS chained_substring_len")
expect(jit).to_contain("PASS chained_substring_starts_with")
expect(jit).to_contain("PASS chained_trim_is_empty")

step("The aggregate verdict line is the authoritative result")
expect(jit).to_contain("CHAINED_BUILTIN_RESULT_TYPE PROBE: ALL PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/chained_builtin_result_type_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering chained builtin method results keep their static type.
- chained builtin method results keep their static type

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6e8ab2377ecfcd8a961586f30e749c0b79238d513567947e77cceb2a505a668f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6e8ab2377ecfcd8a961586f30e749c0b79238d513567947e77cceb2a505a668f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6e8ab2377ecfcd8a961586f30e749c0b79238d513567947e77cceb2a505a668f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/chained_builtin_result_type_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/chained_builtin_result_type_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/chained_builtin_result_type_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/chained_builtin_result_type_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/chained_builtin_result_type_class_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves every chained builtin correctly on the interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/chained_builtin_result_type_class_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves the filed reproducer correctly on the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/chained_builtin_result_type_class_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves the whole chained-builtin class on the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
