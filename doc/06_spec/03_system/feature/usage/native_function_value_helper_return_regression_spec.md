# Native Function Value Helper Return Regression

> This SSpec keeps native helper-returned function values covered after the hybrid-compilability and HIR function-value typing fixes. Both scalar and object-returning function arrays must preserve the returned callable and invoke it correctly in fresh native artifacts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Function Value Helper Return Regression

This SSpec keeps native helper-returned function values covered after the hybrid-compilability and HIR function-value typing fixes. Both scalar and object-returning function arrays must preserve the returned callable and invoke it correctly in fresh native artifacts.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #native-function-value-helper-return-regression |
| Category | Runtime / Native / Function Values |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/08_tracking/bug/native_function_value_helper_return_blocker_2026-06-11.md |
| Source | `test/03_system/feature/usage/native_function_value_helper_return_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec keeps native helper-returned function values covered after the
hybrid-compilability and HIR function-value typing fixes. Both scalar and
object-returning function arrays must preserve the returned callable and invoke
it correctly in fresh native artifacts.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/08_tracking/bug/native_function_value_helper_return_blocker_2026-06-11.md

## Syntax

```sh
src/compiler_rust/target/debug/simple test test/03_system/feature/usage/native_function_value_helper_return_regression_spec.spl --mode=interpreter --clean
```

## Scenarios

### native function value helper return regression

#### keeps scalar and object-returning helper values native and callable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps scalar and object-returning helper values native and callable
- Write the scalar and object-return helper probes
   - Expected: write_code equals `0`
- Compile both probes to standalone native binaries
   - Expected: scalar_compile_code equals `0`
   - Expected: struct_compile_code equals `0`
- The scalar helper-return probe now preserves and invokes the returned function value
   - Expected: scalar_run_code equals `0`
- The object-return helper-return probe also preserves and invokes the returned function value
   - Expected: struct_run_code equals `0`
- The blocker tracker records this boundary as closed
   - Expected: tracker_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps scalar and object-returning helper values native and callable")
step("Write the scalar and object-return helper probes")
val (write_out, write_code) = shell(
    "mkdir -p " + BUILD_DIR +
    " && cat > " + SCALAR_SOURCE + " <<'EOF1'\n" + scalar_probe() + "\nEOF1\n" +
    "cat > " + STRUCT_SOURCE + " <<'EOF2'\n" + struct_probe() + "\nEOF2"
)
expect(write_out.len()).to_be_greater_than(-1)
expect(write_code).to_equal(0)

step("Compile both probes to standalone native binaries")
val (scalar_compile_out, scalar_compile_code) = shell(SIMPLE_BIN + " compile " + SCALAR_SOURCE + " --native -o " + SCALAR_NATIVE)
expect(scalar_compile_code).to_equal(0)
expect(scalar_compile_out).to_contain("Compiled")
val (struct_compile_out, struct_compile_code) = shell(SIMPLE_BIN + " compile " + STRUCT_SOURCE + " --native -o " + STRUCT_NATIVE)
expect(struct_compile_code).to_equal(0)
expect(struct_compile_out).to_contain("Compiled")

step("The scalar helper-return probe now preserves and invokes the returned function value")
val (scalar_run_out, scalar_run_code) = shell(SCALAR_NATIVE)
expect(scalar_run_out).to_contain("got=7")
expect(scalar_run_code).to_equal(0)

step("The object-return helper-return probe also preserves and invokes the returned function value")
val (struct_run_out, struct_run_code) = shell(STRUCT_NATIVE)
expect(struct_run_out).to_contain("done=true")
expect(struct_run_out).to_contain("value=7")
expect(struct_run_code).to_equal(0)

step("The blocker tracker records this boundary as closed")
val (tracker_out, tracker_code) = shell("cat doc/08_tracking/bug/native_function_value_helper_return_blocker_2026-06-11.md")
expect(tracker_code).to_equal(0)
expect(tracker_out).to_contain("Status: closed")
expect(tracker_out).to_contain("scalar and object-returning helper probes")
expect(tracker_out).to_contain("resumable-stepper native crash remains a separate blocker")
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
- **Research:** `doc/08_tracking/bug/native_function_value_helper_return_blocker_2026-06-11.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6d0cacd49e22d8b5676cf0f2bdb4099ae276f2052cad6bf290734f4d3849c6f9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6d0cacd49e22d8b5676cf0f2bdb4099ae276f2052cad6bf290734f4d3849c6f9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6d0cacd49e22d8b5676cf0f2bdb4099ae276f2052cad6bf290734f4d3849c6f9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/usage/native_function_value_helper_return_regression_spec.spl
mirror: doc/06_spec/03_system/feature/usage/native_function_value_helper_return_regression_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/native_function_value_helper_return_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/native_function_value_helper_return_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/native_function_value_helper_return_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/native_function_value_helper_return_regression_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps scalar and object-returning helper values native and callable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
