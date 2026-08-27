# Wide Int Box Roundtrip Class Specification

> Tests covering full-width i64 survives every tagged-slot boxing boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wide Int Box Roundtrip Class Specification

## Scenarios

### full-width i64 survives every tagged-slot boxing boundary

#### keeps every magnitude intact on the interpreter control arm

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps every magnitude intact on the interpreter control arm
- Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter
- The interpreter was correct in all three filed bugs, so a red here means the PROBE is broken, not the engine
- No boundary check may have failed on the control arm
   - Expected: r.0 does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps every magnitude intact on the interpreter control arm")
step("Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter")
val r = run_probe("interpreter")
assert_probe_actually_ran(r.0, r.1)

step("The interpreter was correct in all three filed bugs, so a red here means the PROBE is broken, not the engine")
expect(r.0).to_contain("INTERP_MAX=9223372036854775807")
expect(r.0).to_contain("INTERP_MIN=-9223372036854775808")
expect(r.0).to_contain("INTERP_P60=1152921504606846976")
expect(r.0).to_contain("INTERP_FBITS=4613937818241073152")

step("No boundary check may have failed on the control arm")
expect(r.0.contains("FAIL ")).to_equal(false)
```

</details>

#### keeps every magnitude intact on the cranelift JIT — the engine all three bugs lived in

- keeps every magnitude intact on the cranelift JIT — the engine all three bugs lived in
- Run the same probe under SIMPLE_EXECUTION_MODE=jit
- Boundary 1 — string interpolation. The 2026-07-27 bug printed `-1 0` here
- Boundary 1 must not print the exact truncation signatures the bugs showed
   - Expected: r.0 does not contain `INTERP_MAX=-1`
   - Expected: r.0 does not contain `INTERP_MIN=0`
   - Expected: r.0 does not contain `INTERP_FBITS=2251799813685248`
- Boundary 2 — [i64] array element store/read, at both signs and both extremes
- Boundary 3 — extern-returned i64 through an array, plus the equality the 2026-07-23 bug reported false
- Boundary 4 — nullable `i64?`, a tagged slot by lowering
- Boundary 5 — struct field
- Boundary 6 — untyped `: list` parameter element read, the DECODE half of the same arithmetic
- Aggregate: not a single boundary may have failed
   - Expected: r.0 does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps every magnitude intact on the cranelift JIT — the engine all three bugs lived in")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit")
val r = run_probe("jit")
assert_probe_actually_ran(r.0, r.1)

step("Boundary 1 — string interpolation. The 2026-07-27 bug printed `-1 0` here")
expect(r.0).to_contain("INTERP_MAX=9223372036854775807")
expect(r.0).to_contain("INTERP_MIN=-9223372036854775808")
expect(r.0).to_contain("INTERP_P60=1152921504606846976")
expect(r.0).to_contain("INTERP_N60=-1152921504606846976")
expect(r.0).to_contain("INTERP_FBITS=4613937818241073152")

step("Boundary 1 must not print the exact truncation signatures the bugs showed")
expect(r.0.contains("INTERP_MAX=-1")).to_equal(false)
expect(r.0.contains("INTERP_MIN=0")).to_equal(false)
expect(r.0.contains("INTERP_FBITS=2251799813685248")).to_equal(false)

step("Boundary 2 — [i64] array element store/read, at both signs and both extremes")
expect(r.0).to_contain("PASS array_i64_max")
expect(r.0).to_contain("PASS array_i64_min")
expect(r.0).to_contain("PASS array_i64_p60")
expect(r.0).to_contain("PASS array_i64_n60")
expect(r.0).to_contain("PASS array_i64_fbits")

step("Boundary 3 — extern-returned i64 through an array, plus the equality the 2026-07-23 bug reported false")
expect(r.0).to_contain("PASS extern_f64_bits_direct")
expect(r.0).to_contain("PASS extern_f64_bits_readback")
expect(r.0).to_contain("PASS extern_f64_bits_eq")

step("Boundary 4 — nullable `i64?`, a tagged slot by lowering")
expect(r.0).to_contain("PASS optional_i64_max")
expect(r.0).to_contain("PASS optional_i64_min")

step("Boundary 5 — struct field")
expect(r.0).to_contain("PASS field_i64_max")
expect(r.0).to_contain("PASS field_i64_fbits")

step("Boundary 6 — untyped `: list` parameter element read, the DECODE half of the same arithmetic")
expect(r.0).to_contain("PASS list_param_small")
expect(r.0).to_contain("PASS list_param_max")

step("Aggregate: not a single boundary may have failed")
expect(r.0.contains("FAIL ")).to_equal(false)
```

</details>

#### shows no tag-misread rendering signature under either engine

- shows no tag-misread rendering signature under either engine
- Collect both engines' output
- A tagged word that was never unboxed leaks as `<value:0x..>`
   - Expected: j.0 does not contain `<value:0x`
   - Expected: i.0 does not contain `<value:0x`
- A payload re-read through the float tag renders as a sub-normal double
   - Expected: j.0 does not contain `0.0000000000000000000`
   - Expected: i.0 does not contain `0.0000000000000000000`
- An i64 handed to the heap tag renders as an invalid-heap marker
   - Expected: j.0 does not contain `<invalid-heap:`
   - Expected: i.0 does not contain `<invalid-heap:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shows no tag-misread rendering signature under either engine")
step("Collect both engines' output")
val i = run_probe("interpreter")
val j = run_probe("jit")
assert_probe_actually_ran(i.0, i.1)
assert_probe_actually_ran(j.0, j.1)

step("A tagged word that was never unboxed leaks as `<value:0x..>`")
expect(j.0.contains("<value:0x")).to_equal(false)
expect(i.0.contains("<value:0x")).to_equal(false)

step("A payload re-read through the float tag renders as a sub-normal double")
expect(j.0.contains("0.0000000000000000000")).to_equal(false)
expect(i.0.contains("0.0000000000000000000")).to_equal(false)

step("An i64 handed to the heap tag renders as an invalid-heap marker")
expect(j.0.contains("<invalid-heap:")).to_equal(false)
expect(i.0.contains("<invalid-heap:")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/wide_int_box_roundtrip_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering full-width i64 survives every tagged-slot boxing boundary.
- full-width i64 survives every tagged-slot boxing boundary

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

- Canonical SPipe generation for source `92946d0b3510ee4704d56abdfa63b3dc3271a18b44e927371b3fa207a0751fa0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `92946d0b3510ee4704d56abdfa63b3dc3271a18b44e927371b3fa207a0751fa0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `92946d0b3510ee4704d56abdfa63b3dc3271a18b44e927371b3fa207a0751fa0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/wide_int_box_roundtrip_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/wide_int_box_roundtrip_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/wide_int_box_roundtrip_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/wide_int_box_roundtrip_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/wide_int_box_roundtrip_class_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every magnitude intact on the interpreter control arm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/wide_int_box_roundtrip_class_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every magnitude intact on the cranelift JIT — the engine all three bugs lived in' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/wide_int_box_roundtrip_class_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows no tag-misread rendering signature under either engine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
