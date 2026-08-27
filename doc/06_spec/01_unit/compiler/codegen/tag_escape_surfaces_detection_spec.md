# Tag Escape Surfaces Detection Specification

> Tests covering no derived scalar escapes untagged into a tagged consumer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tag Escape Surfaces Detection Specification

## Scenarios

### no derived scalar escapes untagged into a tagged consumer

#### keeps every surface correct on the interpreter (control arm)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps every surface correct on the interpreter (control arm)
- Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter
- The interpreter is the control: it is correct across this whole class, so a red here means the probe or harness is broken
- Anti-vacuity: the probe must have reached its last check group, not exited early


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps every surface correct on the interpreter (control arm)")
step("Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The interpreter is the control: it is correct across this whole class, so a red here means the probe or harness is broken")
expect(interp).to_contain("TAG_ESCAPE_SURFACES PROBE: ALL PASS")

step("Anti-vacuity: the probe must have reached its last check group, not exited early")
expect(interp).to_contain("PASS residue7_is_15")
```

</details>

#### keeps a derived scalar intact when it is STORED, not just printed

- keeps a derived scalar intact when it is STORED, not just printed
- Run under SIMPLE_EXECUTION_MODE=jit
- An array slot is a genuinely tagged slot — an untagged store corrupts the VALUE, which no amount of formatter fixing would catch


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a derived scalar intact when it is STORED, not just printed")
step("Run under SIMPLE_EXECUTION_MODE=jit")
val jit = run_probe_in_mode("jit")

step("An array slot is a genuinely tagged slot — an untagged store corrupts the VALUE, which no amount of formatter fixing would catch")
expect(jit).to_contain("PASS array_elem0_is_5")
expect(jit).to_contain("PASS array_elem1_is_8")
expect(jit).to_contain("PASS array_elem2_is_300")
```

</details>

#### keeps a derived scalar intact across call and return boundaries

- keeps a derived scalar intact across call and return boundaries
- Run under SIMPLE_EXECUTION_MODE=jit
- Argument slots
- Return slot
- Arithmetic on the derived value, then formatted
- Comparison against a literal — an anti-vacuity control that is green in BOTH states; a red here means the underlying value itself is corrupt


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a derived scalar intact across call and return boundaries")
step("Run under SIMPLE_EXECUTION_MODE=jit")
val jit = run_probe_in_mode("jit")

step("Argument slots")
expect(jit).to_contain("PASS arg_pass_b_is_5")
expect(jit).to_contain("PASS arg_pass_c_is_8")

step("Return slot")
expect(jit).to_contain("PASS return_b_is_5")

step("Arithmetic on the derived value, then formatted")
expect(jit).to_contain("PASS arith_b_plus_c_is_13")

step("Comparison against a literal — an anti-vacuity control that is green in BOTH states; a red here means the underlying value itself is corrupt")
expect(jit).to_contain("PASS compare_b_is_5")
```

</details>

#### covers every low-3-bit residue class, not just the nil one

- covers every low-3-bit residue class, not just the nil one
- Run under SIMPLE_EXECUTION_MODE=jit
- residue 3 is the only bucket the original bug report ever observed; the other seven decode to different, equally silent wrong answers
- A u64 backing store takes a different boxing path and is a separate chance to forget the tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("covers every low-3-bit residue class, not just the nil one")
step("Run under SIMPLE_EXECUTION_MODE=jit")
val jit = run_probe_in_mode("jit")

step("residue 3 is the only bucket the original bug report ever observed; the other seven decode to different, equally silent wrong answers")
expect(jit).to_contain("PASS residue0_is_8")
expect(jit).to_contain("PASS residue1_is_9")
expect(jit).to_contain("PASS residue2_is_10")
expect(jit).to_contain("PASS residue3_is_11")
expect(jit).to_contain("PASS residue4_is_12")
expect(jit).to_contain("PASS residue5_is_13")
expect(jit).to_contain("PASS residue6_is_14")
expect(jit).to_contain("PASS residue7_is_15")

step("A u64 backing store takes a different boxing path and is a separate chance to forget the tag")
expect(jit).to_contain("PASS u64_bitfield_lo_is_9")
expect(jit).to_contain("PASS u64_bitfield_hi_is_17")
```

</details>

#### shows no tag-decode signature under either engine

- shows no tag-decode signature under either engine
- Collect both engines' output
- A raw word read as a heap pointer or an unknown tag renders with a marker
   - Expected: jit does not contain `<value:0x`
   - Expected: jit does not contain `<invalid-heap:0x`
   - Expected: interp does not contain `<value:0x`
   - Expected: interp does not contain `<invalid-heap:0x`
- A raw word read as an inline float renders as a sub-normal double
   - Expected: jit does not contain `0.0000000000000000000`
   - Expected: interp does not contain `0.0000000000000000000`
- The aggregate verdict, and no failing check, under either engine
   - Expected: jit does not contain `FAIL `
   - Expected: interp does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shows no tag-decode signature under either engine")
step("Collect both engines' output")
val interp = run_probe_in_mode("interpreter")
val jit = run_probe_in_mode("jit")

step("A raw word read as a heap pointer or an unknown tag renders with a marker")
expect(jit.contains("<value:0x")).to_equal(false)
expect(jit.contains("<invalid-heap:0x")).to_equal(false)
expect(interp.contains("<value:0x")).to_equal(false)
expect(interp.contains("<invalid-heap:0x")).to_equal(false)

step("A raw word read as an inline float renders as a sub-normal double")
expect(jit.contains("0.0000000000000000000")).to_equal(false)
expect(interp.contains("0.0000000000000000000")).to_equal(false)

step("The aggregate verdict, and no failing check, under either engine")
expect(jit).to_contain("TAG_ESCAPE_SURFACES PROBE: ALL PASS")
expect(jit.contains("FAIL ")).to_equal(false)
expect(interp.contains("FAIL ")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/tag_escape_surfaces_detection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering no derived scalar escapes untagged into a tagged consumer.
- no derived scalar escapes untagged into a tagged consumer

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

- Canonical SPipe generation for source `147db745ead7c4cb77874cbeaa05a14016d96c82d2d6292f74aa0b98f8452547`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `147db745ead7c4cb77874cbeaa05a14016d96c82d2d6292f74aa0b98f8452547`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `147db745ead7c4cb77874cbeaa05a14016d96c82d2d6292f74aa0b98f8452547`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/tag_escape_surfaces_detection_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/tag_escape_surfaces_detection_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/tag_escape_surfaces_detection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/tag_escape_surfaces_detection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/tag_escape_surfaces_detection_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every surface correct on the interpreter (control arm)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/tag_escape_surfaces_detection_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a derived scalar intact when it is STORED, not just printed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/tag_escape_surfaces_detection_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a derived scalar intact across call and return boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
