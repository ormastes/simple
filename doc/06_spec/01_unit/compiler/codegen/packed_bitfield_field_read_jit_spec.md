# Packed Bitfield Field Read Jit Specification

> Tests covering @packed bitfield field reads on the run path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Packed Bitfield Field Read Jit Specification

## Scenarios

### @packed bitfield field reads on the run path

#### reads back the exact register contents under the cranelift JIT

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads back the exact register contents under the cranelift JIT
- Run the run-path probe under SIMPLE_EXECUTION_MODE=jit — the engine the nil reads lived in
- The probe must actually have started, so an empty capture cannot read as a pass
- The original repro: two 1-bit flags set to 1 above a 30-bit reserved field
- The typed form was already correct — it is the control that localises the defect to the erased boundary
- The aggregate verdict line is the authoritative result


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads back the exact register contents under the cranelift JIT")
step("Run the run-path probe under SIMPLE_EXECUTION_MODE=jit — the engine the nil reads lived in")
val jit = run_probe_in_mode("jit")

step("The probe must actually have started, so an empty capture cannot read as a pass")
expect(jit).to_contain("PACKED BITFIELD PROBE START")

step("The original repro: two 1-bit flags set to 1 above a 30-bit reserved field")
expect(jit).to_contain("PASS status_erased_ready")
expect(jit).to_contain("PASS status_erased_readonly")
expect(jit).to_contain("PASS status_erased_reserved")

step("The typed form was already correct — it is the control that localises the defect to the erased boundary")
expect(jit).to_contain("PASS status_typed_ready")
expect(jit).to_contain("PASS status_typed_readonly")
expect(jit).to_contain("PASS status_typed_reserved")

step("The aggregate verdict line is the authoritative result")
expect(jit).to_contain("PACKED BITFIELD PROBE: ALL PASS")
```

</details>

#### generalises across field widths and bit offsets

- generalises across field widths and bit offsets
- Run the probe under the JIT
- Widths 4/12/16 at offsets 0/4/16, each payload chosen with distinct low 3 bits
- A field read must survive arithmetic, not only printing
- A zero-valued field is the case that accidentally survived the original defect; it must stay correct


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("generalises across field widths and bit offsets")
step("Run the probe under the JIT")
val jit = run_probe_in_mode("jit")

step("Widths 4/12/16 at offsets 0/4/16, each payload chosen with distinct low 3 bits")
expect(jit).to_contain("PASS mixed_erased_lo")
expect(jit).to_contain("PASS mixed_erased_mid")
expect(jit).to_contain("PASS mixed_erased_hi")
expect(jit).to_contain("PASS mixed_typed_lo")
expect(jit).to_contain("PASS mixed_typed_mid")
expect(jit).to_contain("PASS mixed_typed_hi")

step("A field read must survive arithmetic, not only printing")
expect(jit).to_contain("PASS mixed_arith")

step("A zero-valued field is the case that accidentally survived the original defect; it must stay correct")
expect(jit).to_contain("PASS status_zero_erased_ready")
expect(jit).to_contain("PASS status_zero_typed_ready")
```

</details>

#### shows no tag-confusion signature and no failed check under the JIT

- shows no tag-confusion signature and no failed check under the JIT
- Collect the JIT output
- A raw word re-read through the tag decoder renders as nil — the exact reported symptom
   - Expected: jit does not contain `nil`
- No check may have failed
   - Expected: jit does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shows no tag-confusion signature and no failed check under the JIT")
step("Collect the JIT output")
val jit = run_probe_in_mode("jit")

step("A raw word re-read through the tag decoder renders as nil — the exact reported symptom")
expect(jit.contains("nil")).to_equal(false)

step("No check may have failed")
expect(jit.contains("FAIL ")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/packed_bitfield_field_read_jit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering @packed bitfield field reads on the run path.
- @packed bitfield field reads on the run path

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

- Canonical SPipe generation for source `519ecdddd65d4eba69af5a6b934845913e901fb9314e3f37c55a7e130e11698e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `519ecdddd65d4eba69af5a6b934845913e901fb9314e3f37c55a7e130e11698e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `519ecdddd65d4eba69af5a6b934845913e901fb9314e3f37c55a7e130e11698e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/packed_bitfield_field_read_jit_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/packed_bitfield_field_read_jit_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/packed_bitfield_field_read_jit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/packed_bitfield_field_read_jit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/packed_bitfield_field_read_jit_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads back the exact register contents under the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/packed_bitfield_field_read_jit_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generalises across field widths and bit offsets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/packed_bitfield_field_read_jit_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows no tag-confusion signature and no failed check under the JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
