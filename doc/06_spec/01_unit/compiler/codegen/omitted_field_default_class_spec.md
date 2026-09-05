# Omitted Field Default Class Specification

> Tests covering omitted declared fields receive their declared default.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Omitted Field Default Class Specification

## Scenarios

### omitted declared fields receive their declared default

#### applies every declared default under the interpreter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- applies every declared default under the interpreter
- Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter
- The interpreter is the control arm — it evaluated declared defaults correctly even before the fix, so a red here means the probe is broken rather than the engine


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("applies every declared default under the interpreter")
step("Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The interpreter is the control arm — it evaluated declared defaults correctly even before the fix, so a red here means the probe is broken rather than the engine")
expect(interp).to_contain("PASS all_omitted_first_field")
expect(interp).to_contain("PASS all_omitted_second_field")
expect(interp).to_contain("OMITTED_FIELD_DEFAULT PROBE: ALL PASS")
```

</details>

#### applies every declared default under the cranelift JIT

- applies every declared default under the cranelift JIT
- Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine the defect lived in
- Axis 1 — the originally reported shape: every field omitted
- Axis 2 — the leak is type-independent: i64, f64, bool and text defaults must all survive
- Axis 3 — a TRAILING run of omitted fields after a positional argument
- Axis 3 — a HOLE left in the middle and at the front by named-argument construction
- Axis 4 — a defaulted field must survive next to one with no declared default
- Name the mechanism directly: no defaulted scalar field may read back as the raw nil tag 3
- The aggregate verdict line is the authoritative result


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("applies every declared default under the cranelift JIT")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine the defect lived in")
val jit = run_probe_in_mode("jit")

step("Axis 1 — the originally reported shape: every field omitted")
expect(jit).to_contain("PASS all_omitted_first_field")
expect(jit).to_contain("PASS all_omitted_second_field")

step("Axis 2 — the leak is type-independent: i64, f64, bool and text defaults must all survive")
expect(jit).to_contain("PASS mixed_i64_default")
expect(jit).to_contain("PASS mixed_f64_default")
expect(jit).to_contain("PASS mixed_bool_default")
expect(jit).to_contain("PASS mixed_text_default")

step("Axis 3 — a TRAILING run of omitted fields after a positional argument")
expect(jit).to_contain("PASS trailing_written")
expect(jit).to_contain("PASS trailing_omitted_b")
expect(jit).to_contain("PASS trailing_omitted_c")

step("Axis 3 — a HOLE left in the middle and at the front by named-argument construction")
expect(jit).to_contain("PASS interleaved_omitted_a")
expect(jit).to_contain("PASS interleaved_written_b")
expect(jit).to_contain("PASS interleaved_omitted_c")

step("Axis 4 — a defaulted field must survive next to one with no declared default")
expect(jit).to_contain("PASS defaulted_beside_plain")

step("Name the mechanism directly: no defaulted scalar field may read back as the raw nil tag 3")
expect(jit).to_contain("PASS no_nil_tag_leak_all_omitted")
expect(jit).to_contain("PASS no_nil_tag_leak_partial")

step("The aggregate verdict line is the authoritative result")
expect(jit).to_contain("OMITTED_FIELD_DEFAULT PROBE: ALL PASS")
```

</details>

#### agrees between the two engines on every field it checks

- agrees between the two engines on every field it checks
- Engine agreement is a SECONDARY check — the absolute-literal assertions above are what prove correctness, since agreement alone would pass while both engines are wrong the same way
   - Expected: jit equals `interp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("agrees between the two engines on every field it checks")
step("Engine agreement is a SECONDARY check — the absolute-literal assertions above are what prove correctness, since agreement alone would pass while both engines are wrong the same way")
val interp = run_probe_in_mode("interpreter")
val jit = run_probe_in_mode("jit")
expect(jit).to_equal(interp)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/omitted_field_default_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering omitted declared fields receive their declared default.
- omitted declared fields receive their declared default

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

- Canonical SPipe generation for source `98ec2f81905b6f5cfe408cc64765a6e006c6ff138a08edab11cd8eaf0a7b57e5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `98ec2f81905b6f5cfe408cc64765a6e006c6ff138a08edab11cd8eaf0a7b57e5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `98ec2f81905b6f5cfe408cc64765a6e006c6ff138a08edab11cd8eaf0a7b57e5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/omitted_field_default_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/omitted_field_default_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/omitted_field_default_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/omitted_field_default_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/omitted_field_default_class_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies every declared default under the interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/omitted_field_default_class_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies every declared default under the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/omitted_field_default_class_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees between the two engines on every field it checks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
