# Option I64 Flat Lane Class Specification

> Tests covering flat primitive-optional lane carries every payload, including the nil sentinel's bit pattern.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Option I64 Flat Lane Class Specification

## Scenarios

### flat primitive-optional lane carries every payload, including the nil sentinel's bit pattern

#### keeps every i64? payload distinct from nil on the interpreter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps every i64? payload distinct from nil on the interpreter
- Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter
- The interpreter is the CONTROL arm — it uses a real Rust Value enum with no in-band sentinel, so a red here means the probe is broken rather than the engine
- The probe must actually have executed its checks, not exited early


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("keeps every i64? payload distinct from nil on the interpreter")
step("Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The interpreter is the CONTROL arm — it uses a real Rust Value enum with no in-band sentinel, so a red here means the probe is broken rather than the engine")
expect(interp).to_contain("OPTION_I64_FLAT_LANE PROBE: ALL PASS")

step("The probe must actually have executed its checks, not exited early")
expect(interp).to_contain("PASS eq_nil_payload_3")
expect(interp).to_contain("PASS coalesce_payload_3")
expect(interp).to_contain("PASS if_val_payload_3")
```

</details>

#### keeps every i64? payload distinct from nil on the cranelift JIT

- keeps every i64? payload distinct from nil on the cranelift JIT
- Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine the defect lives in
- Negative controls: neighbouring payloads must survive, proving the probe reached the JIT and was not silently demoted to the interpreter
- A genuine nil must still read as nil — a fix must not trade this away
- `== nil` must be false for the payload that collides with the sentinel
- `??` is an independent lowering path and must return the payload, not the default
- `if val` is a third independent path and must bind rather than skip the unwrap
- The aggregate verdict line is the authoritative result


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("keeps every i64? payload distinct from nil on the cranelift JIT")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine the defect lives in")
val jit = run_probe_in_mode("jit")

step("Negative controls: neighbouring payloads must survive, proving the probe reached the JIT and was not silently demoted to the interpreter")
expect(jit).to_contain("PASS eq_nil_payload_2")
expect(jit).to_contain("PASS eq_nil_payload_4")
expect(jit).to_contain("PASS eq_nil_payload_11")
expect(jit).to_contain("PASS eq_nil_payload_neg1")

step("A genuine nil must still read as nil — a fix must not trade this away")
expect(jit).to_contain("PASS eq_nil_actual_nil")
expect(jit).to_contain("PASS coalesce_actual_nil")
expect(jit).to_contain("PASS if_val_actual_nil")

step("`== nil` must be false for the payload that collides with the sentinel")
expect(jit).to_contain("PASS eq_nil_payload_3")

step("`??` is an independent lowering path and must return the payload, not the default")
expect(jit).to_contain("PASS coalesce_payload_3")

step("`if val` is a third independent path and must bind rather than skip the unwrap")
expect(jit).to_contain("PASS if_val_payload_3")

step("The aggregate verdict line is the authoritative result")
expect(jit).to_contain("OPTION_I64_FLAT_LANE PROBE: ALL PASS")
```

</details>

#### shows no tag-misread signature under either engine

- shows no tag-misread signature under either engine
- Collect both engines' output
- A raw payload re-read through the runtime's 3-bit tag namespace leaks as `<value:0x..>`
   - Expected: jit does not contain `<value:0x`
   - Expected: interp does not contain `<value:0x`
- No check may have failed under either engine
   - Expected: interp does not contain `FAIL `
   - Expected: jit does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("shows no tag-misread signature under either engine")
step("Collect both engines' output")
val interp = run_probe_in_mode("interpreter")
val jit = run_probe_in_mode("jit")

step("A raw payload re-read through the runtime's 3-bit tag namespace leaks as `<value:0x..>`")
expect(jit.contains("<value:0x")).to_equal(false)
expect(interp.contains("<value:0x")).to_equal(false)

step("No check may have failed under either engine")
expect(interp.contains("FAIL ")).to_equal(false)
expect(jit.contains("FAIL ")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/language/option_i64_flat_lane_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering flat primitive-optional lane carries every payload, including the nil sentinel's bit pattern.
- flat primitive-optional lane carries every payload, including the nil sentinel's bit pattern

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

- `REQ-SSPEC-LANGUAGE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fef014750f05ae270e7f7cf67a17ef9414db1a10e969109765f81129d3e643e2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fef014750f05ae270e7f7cf67a17ef9414db1a10e969109765f81129d3e643e2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fef014750f05ae270e7f7cf67a17ef9414db1a10e969109765f81129d3e643e2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/language/option_i64_flat_lane_class_spec.spl
mirror: doc/06_spec/01_unit/language/option_i64_flat_lane_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/language/option_i64_flat_lane_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/language/option_i64_flat_lane_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/language/option_i64_flat_lane_class_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every i64? payload distinct from nil on the interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/option_i64_flat_lane_class_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every i64? payload distinct from nil on the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/option_i64_flat_lane_class_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows no tag-misread signature under either engine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
