# Native Function Value Array Literal Regression

> This SSpec keeps the fixed lower native path green beneath the hosted `multicore_green` resumable-stepper lane. A plain array literal containing an inline lambda must preserve the function element type, keep the closure unboxed in the array, and call through the array slot with the lambda body return type.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Function Value Array Literal Regression

This SSpec keeps the fixed lower native path green beneath the hosted `multicore_green` resumable-stepper lane. A plain array literal containing an inline lambda must preserve the function element type, keep the closure unboxed in the array, and call through the array slot with the lambda body return type.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #native-function-value-array-literal-regression |
| Category | Runtime / Native / Function Values |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/native_function_value_array_literal_blocker_2026-06-11.md |
| Source | `test/03_system/feature/usage/native_function_value_array_literal_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec keeps the fixed lower native path green beneath the hosted
`multicore_green` resumable-stepper lane. A plain array literal containing
an inline lambda must preserve the function element type, keep the closure
unboxed in the array, and call through the array slot with the lambda body
return type.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/native_function_value_array_literal_blocker_2026-06-11.md

## Syntax

```sh
src/compiler_rust/target/debug/simple test test/03_system/feature/usage/native_function_value_array_literal_regression_spec.spl --mode=interpreter --clean
```

## Scenarios

### native function value array literal regression

#### keeps inline lambda array literal native calls green

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps inline lambda array literal native calls green
- Write the function-value array-literal probe
   - Expected: write_code equals `0`
- Hosted native compile succeeds on the fixed lower path
   - Expected: compile_code equals `0`
- The native probe calls through the array literal and returns the lambda value
   - Expected: native_code equals `0`
- The tracker records the closed lower blocker
   - Expected: blocker_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps inline lambda array literal native calls green")
step("Write the function-value array-literal probe")
val (write_out, write_code) = shell("mkdir -p " + BUILD_DIR + " && cat > " + SOURCE_PATH + " <<'EOF'\n" + probe_source() + "\nEOF")
expect(write_code).to_equal(0)

step("Hosted native compile succeeds on the fixed lower path")
val (compile_out, compile_code) = shell(SIMPLE_BIN + " compile " + SOURCE_PATH + " --native -o " + NATIVE_PATH)
expect(compile_code).to_equal(0)
expect(compile_out).to_contain("Compiled")

step("The native probe calls through the array literal and returns the lambda value")
val (native_out, native_code) = shell("sh -c '" + NATIVE_PATH + " >/tmp/native_fn_array_literal.out 2>&1; code=$?; cat /tmp/native_fn_array_literal.out; echo EXIT=$code'")
expect(native_code).to_equal(0)
expect(native_out).to_contain("before")
expect(native_out).to_contain("value=7")
expect(native_out).to_contain("EXIT=0")

step("The tracker records the closed lower blocker")
val (blocker, blocker_code) = shell("cat doc/08_tracking/bug/native_function_value_array_literal_blocker_2026-06-11.md")
expect(blocker_code).to_equal(0)
expect(blocker).to_contain("Status: closed")
expect(blocker).to_contain("array literal containing function values")
expect(blocker).to_contain("value=7")
expect(blocker).to_contain("EXIT=0")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/multicore_green.md`
- **Plan:** `doc/03_plan/sys_test/multicore_green.md`
- **Design:** `doc/05_design/multicore_green.md`
- **Research:** `doc/08_tracking/bug/native_function_value_array_literal_blocker_2026-06-11.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `76906a3ab236a150855d65f763a5680eec46ed456bcf1926cebd60f9a8b2d0d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `76906a3ab236a150855d65f763a5680eec46ed456bcf1926cebd60f9a8b2d0d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `76906a3ab236a150855d65f763a5680eec46ed456bcf1926cebd60f9a8b2d0d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/usage/native_function_value_array_literal_regression_spec.spl
mirror: doc/06_spec/03_system/feature/usage/native_function_value_array_literal_regression_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/native_function_value_array_literal_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/native_function_value_array_literal_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/native_function_value_array_literal_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/native_function_value_array_literal_regression_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps inline lambda array literal native calls green' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
