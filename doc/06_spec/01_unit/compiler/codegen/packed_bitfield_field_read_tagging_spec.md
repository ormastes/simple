# Packed Bitfield Field Read Tagging Specification

> Tests covering packed bitfield field reads are tagged before formatting.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Packed Bitfield Field Read Tagging Specification

## Scenarios

### packed bitfield field reads are tagged before formatting

#### reads every bitfield through the interpreter (control arm)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads every bitfield through the interpreter (control arm)
- Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter
- The interpreter was correct in the original report — a red here means the probe or harness is broken, not the JIT
- The probe must actually have executed its checks, not exited early


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads every bitfield through the interpreter (control arm)")
step("Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The interpreter was correct in the original report — a red here means the probe or harness is broken, not the JIT")
expect(interp).to_contain("PACKED_BITFIELD_READ PROBE: ALL PASS")

step("The probe must actually have executed its checks, not exited early")
expect(interp).to_contain("PASS bitfield_bit0_is_1")
expect(interp).to_contain("PASS bitfield_byte1_is_9")
```

</details>

#### reads every bitfield through the cranelift JIT

- reads every bitfield through the cranelift JIT
- Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine the bug lived in
- The exact expression from the bug report: a 1-bit field holding 1 printed `nil`
- A zero-valued wide field always rendered correctly and must keep doing so
- Byte-wide fields at offsets 0/8/16 — these printed <value:0x5> and <invalid-heap:0x9>
- The quietest form: a multiple of 8 has tag bits 0, so it came back silently divided by 8 (8 printed as 1) with no marker text
- Control: an ordinary non-bitfield u32 struct field was never broken
- The documented workaround — routing the read through a local — must keep working
- The aggregate verdict line is the authoritative result


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads every bitfield through the cranelift JIT")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine the bug lived in")
val jit = run_probe_in_mode("jit")

step("The exact expression from the bug report: a 1-bit field holding 1 printed `nil`")
expect(jit).to_contain("PASS bitfield_bit0_is_1")
expect(jit).to_contain("PASS bitfield_bit1_is_1")

step("A zero-valued wide field always rendered correctly and must keep doing so")
expect(jit).to_contain("PASS bitfield_wide_is_0")

step("Byte-wide fields at offsets 0/8/16 — these printed <value:0x5> and <invalid-heap:0x9>")
expect(jit).to_contain("PASS bitfield_byte0_is_5")
expect(jit).to_contain("PASS bitfield_byte1_is_9")
expect(jit).to_contain("PASS bitfield_word_is_300")

step("The quietest form: a multiple of 8 has tag bits 0, so it came back silently divided by 8 (8 printed as 1) with no marker text")
expect(jit).to_contain("PASS bitfield_byte0_is_8")

step("Control: an ordinary non-bitfield u32 struct field was never broken")
expect(jit).to_contain("PASS plain_u32_field_is_7")

step("The documented workaround — routing the read through a local — must keep working")
expect(jit).to_contain("PASS bitfield_via_local_is_1")

step("The aggregate verdict line is the authoritative result")
expect(jit).to_contain("PACKED_BITFIELD_READ PROBE: ALL PASS")
```

</details>

#### leaks no untagged word under either engine

- leaks no untagged word under either engine
- Collect both engines' output
- A raw word reaching the formatter renders with one of these tag-decode markers
   - Expected: jit does not contain `<value:0x`
   - Expected: jit does not contain `<invalid-heap:0x`
   - Expected: interp does not contain `<value:0x`
   - Expected: interp does not contain `<invalid-heap:0x`
- No check may have failed under either engine
   - Expected: jit does not contain `FAIL `
   - Expected: interp does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaks no untagged word under either engine")
step("Collect both engines' output")
val interp = run_probe_in_mode("interpreter")
val jit = run_probe_in_mode("jit")

step("A raw word reaching the formatter renders with one of these tag-decode markers")
expect(jit.contains("<value:0x")).to_equal(false)
expect(jit.contains("<invalid-heap:0x")).to_equal(false)
expect(interp.contains("<value:0x")).to_equal(false)
expect(interp.contains("<invalid-heap:0x")).to_equal(false)

step("No check may have failed under either engine")
expect(jit.contains("FAIL ")).to_equal(false)
expect(interp.contains("FAIL ")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/packed_bitfield_field_read_tagging_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering packed bitfield field reads are tagged before formatting.
- packed bitfield field reads are tagged before formatting

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

- Canonical SPipe generation for source `dcee0ac3ef17b63c1eceb4f59d3aac8f79a4154067a0d5d5559be852813301f4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dcee0ac3ef17b63c1eceb4f59d3aac8f79a4154067a0d5d5559be852813301f4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dcee0ac3ef17b63c1eceb4f59d3aac8f79a4154067a0d5d5559be852813301f4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/packed_bitfield_field_read_tagging_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/packed_bitfield_field_read_tagging_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/packed_bitfield_field_read_tagging_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/packed_bitfield_field_read_tagging_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/packed_bitfield_field_read_tagging_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads every bitfield through the interpreter (control arm)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/packed_bitfield_field_read_tagging_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads every bitfield through the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/packed_bitfield_field_read_tagging_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaks no untagged word under either engine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
