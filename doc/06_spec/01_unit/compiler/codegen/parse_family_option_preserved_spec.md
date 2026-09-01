# Parse Family Option Preserved Specification

> Tests covering text parse_* returns an Option on every engine.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parse Family Option Preserved Specification

## Scenarios

### text parse_* returns an Option on every engine

#### returns Some/None from parse_int on the interpreter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns Some/None from parse_int on the interpreter
- Run the probe under SIMPLE_EXECUTION_MODE=interpreter
- The interpreter was correct before the fix, so it is the control arm: a red here means the probe is broken rather than the engine


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns Some/None from parse_int on the interpreter")
step("Run the probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The interpreter was correct before the fix, so it is the control arm: a red here means the probe is broken rather than the engine")
expect(interp).to_contain("PASS parse_int_some_is_some")
expect(interp).to_contain("PASS parse_int_none_is_some")
expect(interp).to_contain("PARSE_FAMILY_OPTION PROBE: ALL PASS")
```

</details>

#### returns Some/None from parse_int on the cranelift JIT

- returns Some/None from parse_int on the cranelift JIT
- Run the same probe under SIMPLE_EXECUTION_MODE=jit -- the engine the defect lived in
- `"42".parse_int()` must be a Some, not the bare integer 42. Pre-fix this printed `FAIL parse_int_some_is_some`, because `.is_some()` was being called on an i64
- `"abc".parse_int()` must be None, and must stay distinguishable from `"0".parse_int()` -- the property a bare i64 return cannot have


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns Some/None from parse_int on the cranelift JIT")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit -- the engine the defect lived in")
val jit = run_probe_in_mode("jit")

step("`\"42\".parse_int()` must be a Some, not the bare integer 42. Pre-fix this printed `FAIL parse_int_some_is_some`, because `.is_some()` was being called on an i64")
expect(jit).to_contain("PASS parse_int_some_is_some")
expect(jit).to_contain("PASS parse_int_some_unwrap")

step("`\"abc\".parse_int()` must be None, and must stay distinguishable from `\"0\".parse_int()` -- the property a bare i64 return cannot have")
expect(jit).to_contain("PASS parse_int_none_is_some")
expect(jit).to_contain("PASS parse_int_zero_is_some")
expect(jit).to_contain("PASS parse_int_zero_unwrap")
```

</details>

#### applies the unwrap_or default to an absent optional

- applies the unwrap_or default to an absent optional
- Run the probe under the JIT
- `.unwrap_or(-1)` on an absent optional must yield -1, not nil
- The nil control never touches parse_int, so if it fails too the defect is in unwrap_or rather than in the parse family


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("applies the unwrap_or default to an absent optional")
# KNOWN RED on the JIT arm. This asserts correct behaviour that the JIT
# does not yet have, and is deliberately left failing rather than
# weakened, per .claude/rules/testing.md.
# doc/08_tracking/bug/jit_unwrap_or_on_absent_optional_ignores_default_2026-08-17.md
step("Run the probe under the JIT")
val jit = run_probe_in_mode("jit")

step("`.unwrap_or(-1)` on an absent optional must yield -1, not nil")
expect(jit).to_contain("PASS unwrap_or_absent_default")

step("The nil control never touches parse_int, so if it fails too the defect is in unwrap_or rather than in the parse family")
expect(jit).to_contain("PASS nil_unwrap_or_default")
```

</details>

#### resolves every spelling of the int parse method on the JIT

- resolves every spelling of the int parse method on the JIT
- Run the probe under the JIT
- `parse_i64` and `parse_i32` were not routed at all pre-fix: the probe died on `Function 'str.parse_i64' not found`
- No unresolved-dispatch error may appear
   - Expected: jit does not contain `not found`
   - Expected: jit does not contain `unresolved symbol`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves every spelling of the int parse method on the JIT")
step("Run the probe under the JIT")
val jit = run_probe_in_mode("jit")

step("`parse_i64` and `parse_i32` were not routed at all pre-fix: the probe died on `Function 'str.parse_i64' not found`")
expect(jit).to_contain("PASS parse_i64_some_is_some")
expect(jit).to_contain("PASS parse_i32_some_is_some")
expect(jit).to_contain("PASS parse_i64_none_is_some")

step("No unresolved-dispatch error may appear")
expect(jit.contains("not found")).to_equal(false)
expect(jit.contains("unresolved symbol")).to_equal(false)
```

</details>

#### keeps the total to_* family total rather than converting it to Options

- keeps the total to_* family total rather than converting it to Options
- Run the probe under the JIT
- `to_int`/`to_i64`/`to_float` are specified to be TOTAL and yield 0 on failure. Turning them into Options would have been the lazy way to fix the parse family and would break every caller, so the fix is pinned from both sides


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the total to_* family total rather than converting it to Options")
step("Run the probe under the JIT")
val jit = run_probe_in_mode("jit")

step("`to_int`/`to_i64`/`to_float` are specified to be TOTAL and yield 0 on failure. Turning them into Options would have been the lazy way to fix the parse family and would break every caller, so the fix is pinned from both sides")
expect(jit).to_contain("PASS to_int_ok")
expect(jit).to_contain("PASS to_int_failure_is_zero")
expect(jit).to_contain("PASS to_float_failure_is_zero")
expect(jit).to_contain("PASS int_cast_ok")
```

</details>

#### shows no failing check under either engine

- shows no failing check under either engine
- Collect both engines
- A single FAIL line means the probe found a wrong answer
   - Expected: jit does not contain `FAIL parse_`
   - Expected: interp does not contain `FAIL `
- An empty capture would make every `contains(...) == false` above vacuously true, so require the verdict line on both arms


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shows no failing check under either engine")
step("Collect both engines")
val interp = run_probe_in_mode("interpreter")
val jit = run_probe_in_mode("jit")

step("A single FAIL line means the probe found a wrong answer")
expect(jit.contains("FAIL parse_")).to_equal(false)
expect(interp.contains("FAIL ")).to_equal(false)

step("An empty capture would make every `contains(...) == false` above vacuously true, so require the verdict line on both arms")
expect(jit).to_contain("PARSE_FAMILY_OPTION PROBE:")
expect(interp).to_contain("PARSE_FAMILY_OPTION PROBE:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/parse_family_option_preserved_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering text parse_* returns an Option on every engine.
- text parse_* returns an Option on every engine

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

- Canonical SPipe generation for source `d0ee0e011f40ef47765beec45a3d3b570475f878a0518f30bc5c1fbc9022a165`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d0ee0e011f40ef47765beec45a3d3b570475f878a0518f30bc5c1fbc9022a165`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d0ee0e011f40ef47765beec45a3d3b570475f878a0518f30bc5c1fbc9022a165`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/parse_family_option_preserved_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/parse_family_option_preserved_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/parse_family_option_preserved_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/parse_family_option_preserved_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/parse_family_option_preserved_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns Some/None from parse_int on the interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/parse_family_option_preserved_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns Some/None from parse_int on the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/parse_family_option_preserved_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies the unwrap_or default to an absent optional' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
