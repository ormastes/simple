# Coalesce Sentinel Collision Class Specification

> Tests covering `??` never mistakes a real scalar for the nil sentinel.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coalesce Sentinel Collision Class Specification

## Scenarios

### `??` never mistakes a real scalar for the nil sentinel

#### keeps every low-3-bit value intact under the interpreter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps every low-3-bit value intact under the interpreter
- Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter
- The interpreter is the control arm — it holds a typed Value and never reaches the raw-word comparison, so a red here means the probe itself is broken
- The probe must actually have executed, not exited early


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps every low-3-bit value intact under the interpreter")
step("Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The interpreter is the control arm — it holds a typed Value and never reaches the raw-word comparison, so a red here means the probe itself is broken")
expect(interp).to_contain("COALESCE_SENTINEL PROBE: ALL PASS")

step("The probe must actually have executed, not exited early")
expect(interp).to_contain("PASS scalar_3")
expect(interp).to_contain("PASS index_of_coalesce")
```

</details>

#### keeps every low-3-bit value intact under the cranelift JIT

- keeps every low-3-bit value intact under the cranelift JIT
- Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine the defect lived in
- Sweep every tag bit pattern 0..8 as a plain local; 0 (SPECIAL_NIL) and 3 (TAG_SPECIAL) are the historically fatal two
- The original reporter's shape: a search result that happens to be 3
- Derived and negative values take the same path
- The opposite failure mode: a genuinely-absent accessor must still yield the default, never leak the raw sentinel 3 as an integer
- And a PRESENT accessor result whose value IS a sentinel must survive — this is the half the static lower_coalesce fix deliberately does not cover (see doc/08_tracking/bug/coalesce_optional_accessor_sentinel_value_eaten_jit_2026-08-17.md)
- The aggregate verdict line is the authoritative result


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps every low-3-bit value intact under the cranelift JIT")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit — the engine the defect lived in")
val jit = run_probe_in_mode("jit")

step("Sweep every tag bit pattern 0..8 as a plain local; 0 (SPECIAL_NIL) and 3 (TAG_SPECIAL) are the historically fatal two")
expect(jit).to_contain("PASS scalar_0")
expect(jit).to_contain("PASS scalar_3")
expect(jit).to_contain("PASS scalar_7")

step("The original reporter's shape: a search result that happens to be 3")
expect(jit).to_contain("PASS index_of_coalesce")

step("Derived and negative values take the same path")
expect(jit).to_contain("PASS scalar_derived3")
expect(jit).to_contain("PASS scalar_neg3")

step("The opposite failure mode: a genuinely-absent accessor must still yield the default, never leak the raw sentinel 3 as an integer")
expect(jit).to_contain("PASS empty_first_default")
expect(jit).to_contain("PASS oob_get_default")

step("And a PRESENT accessor result whose value IS a sentinel must survive — this is the half the static lower_coalesce fix deliberately does not cover (see doc/08_tracking/bug/coalesce_optional_accessor_sentinel_value_eaten_jit_2026-08-17.md)")
expect(jit).to_contain("PASS present_first_is_3")
expect(jit).to_contain("PASS present_get_is_0")

step("The aggregate verdict line is the authoritative result")
expect(jit).to_contain("COALESCE_SENTINEL PROBE: ALL PASS")
```

</details>

#### shows no sentinel-substitution signature under either engine

- shows no sentinel-substitution signature under either engine
- Collect both engines' output
- No check may have failed under either engine
   - Expected: jit does not contain `FAIL `
   - Expected: interp does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shows no sentinel-substitution signature under either engine")
step("Collect both engines' output")
val interp = run_probe_in_mode("interpreter")
val jit = run_probe_in_mode("jit")

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
| Source | `test/01_unit/compiler/codegen/coalesce_sentinel_collision_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering `??` never mistakes a real scalar for the nil sentinel.
- `??` never mistakes a real scalar for the nil sentinel

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

- Canonical SPipe generation for source `5bc16512d9fa33ae8f41c2f6d5577e7c21715a71b956eb5d145a3de4d0d66d42`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5bc16512d9fa33ae8f41c2f6d5577e7c21715a71b956eb5d145a3de4d0d66d42`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5bc16512d9fa33ae8f41c2f6d5577e7c21715a71b956eb5d145a3de4d0d66d42`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/coalesce_sentinel_collision_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/coalesce_sentinel_collision_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/coalesce_sentinel_collision_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/coalesce_sentinel_collision_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/coalesce_sentinel_collision_class_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every low-3-bit value intact under the interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/coalesce_sentinel_collision_class_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every low-3-bit value intact under the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/coalesce_sentinel_collision_class_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows no sentinel-substitution signature under either engine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
