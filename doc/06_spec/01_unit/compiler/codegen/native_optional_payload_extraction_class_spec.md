# Native Optional Payload Extraction Class Specification

> Tests covering optional payload extraction across representation, type and spelling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Optional Payload Extraction Class Specification

## Scenarios

### optional payload extraction across representation, type and spelling

#### extracts every optional payload correctly on the interpreter (control arm)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts every optional payload correctly on the interpreter (control arm)
- Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter
- The interpreter was never affected by this family — a red here means the probe itself is broken, not the engine
- Confirm the probe actually executed rather than exiting early


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("extracts every optional payload correctly on the interpreter (control arm)")
step("Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The interpreter was never affected by this family — a red here means the probe itself is broken, not the engine")
expect(interp).to_contain("OPTIONAL_PAYLOAD PROBE: ALL PASS")

step("Confirm the probe actually executed rather than exiting early")
expect(interp).to_contain("PASS ifval_pair_i64_f0")
expect(interp).to_contain("PASS boxed_ifval_sugar")
```

</details>

#### extracts raw-form tuple payloads on the JIT lane (the filed regression)

- extracts raw-form tuple payloads on the JIT lane (the filed regression)
- Run the same probe under SIMPLE_EXECUTION_MODE=jit — the lane the bug lived on
- Both fields of a raw-form (i64,i64)? bound via `if val Some(p)` — these read the nil sentinel 3 before the fix
- A mixed (text,i64)? tuple, and the match-arm spelling of the same extraction
- nil detection must still work — it was already correct and must not regress


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("extracts raw-form tuple payloads on the JIT lane (the filed regression)")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit — the lane the bug lived on")
val jit = run_probe_in_mode("jit")

step("Both fields of a raw-form (i64,i64)? bound via `if val Some(p)` — these read the nil sentinel 3 before the fix")
expect(jit).to_contain("PASS ifval_pair_i64_f0")
expect(jit).to_contain("PASS ifval_pair_i64_f1")

step("A mixed (text,i64)? tuple, and the match-arm spelling of the same extraction")
expect(jit).to_contain("PASS ifval_pair_mixed_f0")
expect(jit).to_contain("PASS match_pair_i64_f0")
expect(jit).to_contain("PASS match_pair_i64_f1")

step("nil detection must still work — it was already correct and must not regress")
expect(jit).to_contain("PASS nil_pair_none_arm")
expect(jit).to_contain("PASS nil_scalar_none_arm")
```

</details>

#### generalises to every scalar payload type, not just tuples

- generalises to every scalar payload type, not just tuples
- The raw migration form is not tuple-specific: any payload type hits the same extraction path


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("generalises to every scalar payload type, not just tuples")
step("The raw migration form is not tuple-specific: any payload type hits the same extraction path")
val jit = run_probe_in_mode("jit")

expect(jit).to_contain("PASS ifval_scalar_i64")
expect(jit).to_contain("PASS ifval_scalar_text")
expect(jit).to_contain("PASS ifval_scalar_bool")
expect(jit).to_contain("PASS ifval_scalar_f64")
expect(jit).to_contain("PASS match_scalar_i64")
```

</details>

#### generalises to every consumption spelling, boxed representation included

- generalises to every consumption spelling, boxed representation included
- A literal Some(99) is a real heap enum — the boxed arm must stay byte-identical to the legacy path
- Pattern spellings, lowered by build_pattern_binding_stmts
- Sugar spellings, lowered by expr/control.rs — these are the members the tuple reproducer never reached


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("generalises to every consumption spelling, boxed representation included")
step("A literal Some(99) is a real heap enum — the boxed arm must stay byte-identical to the legacy path")
val jit = run_probe_in_mode("jit")

step("Pattern spellings, lowered by build_pattern_binding_stmts")
expect(jit).to_contain("PASS boxed_match_some")
expect(jit).to_contain("PASS boxed_ifval_some_pattern")

step("Sugar spellings, lowered by expr/control.rs — these are the members the tuple reproducer never reached")
expect(jit).to_contain("PASS boxed_ifval_sugar")
expect(jit).to_contain("PASS boxed_coalesce")
```

</details>

#### shows no representation-confusion signature under either engine

- shows no representation-confusion signature under either engine
- Collect both engines' output
- An enum handle that leaked instead of its payload renders as `<enum@0x..`
   - Expected: jit does not contain `<enum@0x`
   - Expected: interp does not contain `<enum@0x`
- A payload read through the nil sentinel renders as the bare integer 3 — the probe reports it as a FAIL line
   - Expected: jit does not contain `FAIL `
   - Expected: interp does not contain `FAIL `
- The aggregate verdict line is the authoritative result for both engines


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shows no representation-confusion signature under either engine")
step("Collect both engines' output")
val interp = run_probe_in_mode("interpreter")
val jit = run_probe_in_mode("jit")

step("An enum handle that leaked instead of its payload renders as `<enum@0x..`")
expect(jit.contains("<enum@0x")).to_equal(false)
expect(interp.contains("<enum@0x")).to_equal(false)

step("A payload read through the nil sentinel renders as the bare integer 3 — the probe reports it as a FAIL line")
expect(jit.contains("FAIL ")).to_equal(false)
expect(interp.contains("FAIL ")).to_equal(false)

step("The aggregate verdict line is the authoritative result for both engines")
expect(jit).to_contain("OPTIONAL_PAYLOAD PROBE: ALL PASS")
expect(interp).to_contain("OPTIONAL_PAYLOAD PROBE: ALL PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/native_optional_payload_extraction_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering optional payload extraction across representation, type and spelling.
- optional payload extraction across representation, type and spelling

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

- Canonical SPipe generation for source `79949df774c7eebdd8d22b40347325107e4b33c0aa6d37e28f7487ba9882e0b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `79949df774c7eebdd8d22b40347325107e4b33c0aa6d37e28f7487ba9882e0b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `79949df774c7eebdd8d22b40347325107e4b33c0aa6d37e28f7487ba9882e0b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/native_optional_payload_extraction_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/native_optional_payload_extraction_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/native_optional_payload_extraction_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/native_optional_payload_extraction_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/native_optional_payload_extraction_class_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts every optional payload correctly on the interpreter (control arm)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/native_optional_payload_extraction_class_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts raw-form tuple payloads on the JIT lane (the filed regression)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/native_optional_payload_extraction_class_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generalises to every scalar payload type, not just tuples' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
