# Rt Nil Sentinel Collision Class Specification

> Tests covering RT_NIL sentinel (raw word 3) must never collide with the integer 3.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rt Nil Sentinel Collision Class Specification

## Scenarios

### RT_NIL sentinel (raw word 3) must never collide with the integer 3

#### passes the whole class on the tree-walk interpreter (control arm)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- passes the whole class on the tree-walk interpreter (control arm)
- Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter
- The interpreter carries a real type tag and was correct in both filed bugs, so a red here means the PROBE is broken, not the engine
- The probe must actually have run its checks rather than exiting early


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes the whole class on the tree-walk interpreter (control arm)")
step("Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode(PROBE_PATH, "interpreter")

step("The interpreter carries a real type tag and was correct in both filed bugs, so a red here means the PROBE is broken, not the engine")
expect(interp).to_contain("RT_NIL_SENTINEL PROBE: ALL PASS")

step("The probe must actually have run its checks rather than exiting early")
expect(interp).to_contain("PASS raw_coalesce_3")
expect(interp).to_contain("PASS array_get_miss_bare")
expect(interp).to_contain("PASS present_3_get_coalesce")
```

</details>

#### never treats a RAW scalar equal to the sentinel as nil (direction: raw -> boxed)

- never treats a RAW scalar equal to the sentinel as nil (direction: raw -> boxed)
- Run the same probe under the cranelift JIT — the engine both bugs lived in
- A non-nullable scalar can never legitimately be nil, so `?? d` is the identity for EVERY value
- The sentinel-adjacent neighbours a future encoding change would break next: 0, the tagged bool words 11/19, and 24 which is the correct BOXING of 3
- The other scalar lanes that share the untagged representation


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("never treats a RAW scalar equal to the sentinel as nil (direction: raw -> boxed)")
step("Run the same probe under the cranelift JIT — the engine both bugs lived in")
val jit = run_probe_in_mode(PROBE_PATH, "jit")

step("A non-nullable scalar can never legitimately be nil, so `?? d` is the identity for EVERY value")
expect(jit).to_contain("PASS raw_coalesce_3")
expect(jit).to_contain("PASS raw_coalesce_computed3")
expect(jit).to_contain("PASS raw_coalesce_neg3")

step("The sentinel-adjacent neighbours a future encoding change would break next: 0, the tagged bool words 11/19, and 24 which is the correct BOXING of 3")
expect(jit).to_contain("PASS raw_coalesce_0")
expect(jit).to_contain("PASS raw_coalesce_11")
expect(jit).to_contain("PASS raw_coalesce_19")
expect(jit).to_contain("PASS raw_coalesce_24")

step("The other scalar lanes that share the untagged representation")
expect(jit).to_contain("PASS raw_coalesce_u8_3")
expect(jit).to_contain("PASS raw_coalesce_i32_3")
expect(jit).to_contain("PASS raw_coalesce_bool")
```

</details>

#### never leaks the boxed sentinel as the integer 3 (direction: boxed -> raw)

- never leaks the boxed sentinel as the integer 3 (direction: boxed -> raw)
- An array `.get()` miss must FORMAT as nil, not as the raw sentinel word
- A dict miss and the empty-receiver first/last accessors take the same producer path


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("never leaks the boxed sentinel as the integer 3 (direction: boxed -> raw)")
val jit = run_probe_in_mode(PROBE_PATH, "jit")

step("An array `.get()` miss must FORMAT as nil, not as the raw sentinel word")
expect(jit).to_contain("PASS array_get_miss_bare")
expect(jit).to_contain("PASS array_get_miss_far")
expect(jit).to_contain("PASS empty_get_miss_bare")

step("A dict miss and the empty-receiver first/last accessors take the same producer path")
expect(jit).to_contain("PASS dict_get_miss_bare")
expect(jit).to_contain("PASS empty_first_coalesce")
expect(jit).to_contain("PASS empty_last_coalesce")
```

</details>

#### leaves a genuinely PRESENT 3 untouched on every one of those same paths (discriminator)

- leaves a genuinely PRESENT 3 untouched on every one of those same paths (discriminator)
- This arm is what separates a real fix from one that merely rewrites every 3 to nil
- A negative index is a supported Python-style wrap, not an out-of-bounds access
- Every small present value read back through the array-element path


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaves a genuinely PRESENT 3 untouched on every one of those same paths (discriminator)")
val jit = run_probe_in_mode(PROBE_PATH, "jit")

step("This arm is what separates a real fix from one that merely rewrites every 3 to nil")
expect(jit).to_contain("PASS present_3_index")
expect(jit).to_contain("PASS present_3_get_bare")
expect(jit).to_contain("PASS present_3_get_coalesce")
expect(jit).to_contain("PASS present_3_first")
expect(jit).to_contain("PASS present_3_last")
expect(jit).to_contain("PASS present_3_dict_bare")
expect(jit).to_contain("PASS present_3_dict_coalesce")

step("A negative index is a supported Python-style wrap, not an out-of-bounds access")
expect(jit).to_contain("PASS present_3_neg_index")

step("Every small present value read back through the array-element path")
expect(jit).to_contain("PASS sweep_present_3")
expect(jit).to_contain("PASS sweep_present_0")
expect(jit).to_contain("PASS sweep_present_24")
```

</details>

#### reports one aggregate verdict with no failing row under either engine

- reports one aggregate verdict with no failing row under either engine
- The aggregate verdict line is the authoritative result
- No individual check may have failed
   - Expected: jit does not contain `FAIL `
   - Expected: interp does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports one aggregate verdict with no failing row under either engine")
val jit = run_probe_in_mode(PROBE_PATH, "jit")
val interp = run_probe_in_mode(PROBE_PATH, "interpreter")

step("The aggregate verdict line is the authoritative result")
expect(jit).to_contain("RT_NIL_SENTINEL PROBE: ALL PASS")
expect(interp).to_contain("RT_NIL_SENTINEL PROBE: ALL PASS")

step("No individual check may have failed")
expect(jit.contains("FAIL ")).to_equal(false)
expect(interp.contains("FAIL ")).to_equal(false)
```

</details>

#### fails a bare out-of-bounds index loudly instead of returning the sentinel

- fails a bare out-of-bounds index loudly instead of returning the sentinel
- Run the dedicated bare-OOB probe, split out because the correct behaviour terminates the process
- `xs[9]` on a 3-element array must not exit 0 — the filed bug recorded rc=0 with no panic
   - Expected: jit does not contain `RC=0`
- The interpreter is the control arm: it already panics with `array index out of bounds`
   - Expected: interp does not contain `RC=0`
- Execution must not have reached the marker line past the faulting index
   - Expected: jit_out does not contain `BARE_OOB PROBE: NO PANIC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails a bare out-of-bounds index loudly instead of returning the sentinel")
step("Run the dedicated bare-OOB probe, split out because the correct behaviour terminates the process")
val jit = run_oob_probe_rc("jit")

step("`xs[9]` on a 3-element array must not exit 0 — the filed bug recorded rc=0 with no panic")
expect(jit.contains("RC=0")).to_equal(false)

step("The interpreter is the control arm: it already panics with `array index out of bounds`")
val interp = run_oob_probe_rc("interpreter")
expect(interp.contains("RC=0")).to_equal(false)

step("Execution must not have reached the marker line past the faulting index")
val jit_out = run_probe_in_mode(OOB_PROBE_PATH, "jit")
expect(jit_out.contains("BARE_OOB PROBE: NO PANIC")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/rt_nil_sentinel_collision_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RT_NIL sentinel (raw word 3) must never collide with the integer 3.
- RT_NIL sentinel (raw word 3) must never collide with the integer 3

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `d5299819f06d9d059b5d6a6110d3c771b8621f3667b58131df3b8256621356c0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d5299819f06d9d059b5d6a6110d3c771b8621f3667b58131df3b8256621356c0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d5299819f06d9d059b5d6a6110d3c771b8621f3667b58131df3b8256621356c0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/rt_nil_sentinel_collision_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/rt_nil_sentinel_collision_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/rt_nil_sentinel_collision_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/rt_nil_sentinel_collision_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/rt_nil_sentinel_collision_class_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes the whole class on the tree-walk interpreter (control arm)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/rt_nil_sentinel_collision_class_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never treats a RAW scalar equal to the sentinel as nil (direction: raw -> boxed)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/rt_nil_sentinel_collision_class_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never leaks the boxed sentinel as the integer 3 (direction: boxed -> raw)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
