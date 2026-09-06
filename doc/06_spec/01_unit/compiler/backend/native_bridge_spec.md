# native_bridge_spec

> Purpose: Prove that Native Bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_bridge_spec

Purpose: Prove that Native Bridge.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native_bridge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Native Bridge.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### Native Bridge

#### builds compile result values for success and failure

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds compile result values for success and failure
- Verify: builds compile result values for success and failure
   - Expected: success.success is true
   - Expected: success.binary_path equals `/tmp/native-bin`
   - Expected: success.error_message equals ``
   - Expected: success.compile_time_ms equals `123`
   - Expected: failure.success is false
   - Expected: failure.binary_path equals ``
   - Expected: failure.error_message equals `linker failed`
   - Expected: failure.compile_time_ms equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("builds compile result values for success and failure")
step("Verify: builds compile result values for success and failure")
# @req: REQ-COMP-NATIVE-BRIDGE-001
val success = nativecompileresult_success_result("/tmp/native-bin", 123)
val failure = nativecompileresult_error_result("linker failed")

expect(success.success).to_equal(true)
expect(success.binary_path).to_equal("/tmp/native-bin")
expect(success.error_message).to_equal("")
expect(success.compile_time_ms).to_equal(123)

expect(failure.success).to_equal(false)
expect(failure.binary_path).to_equal("")
expect(failure.error_message).to_equal("linker failed")
expect(failure.compile_time_ms).to_equal(0)
```

</details>

#### preserves execution result fields on hand-built values

- preserves execution result fields on hand-built values
- Verify: preserves execution result fields on hand-built values
   - Expected: result.stdout equals `stdout text`
   - Expected: result.stderr equals `stderr text`
   - Expected: result.exit_code equals `7`
   - Expected: result.execution_time_ms equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves execution result fields on hand-built values")
step("Verify: preserves execution result fields on hand-built values")
val result = NativeExecutionResult(
    stdout: "stdout text",
    stderr: "stderr text",
    exit_code: 7,
    execution_time_ms: 42
)

expect(result.stdout).to_equal("stdout text")
expect(result.stderr).to_equal("stderr text")
expect(result.exit_code).to_equal(7)
expect(result.execution_time_ms).to_equal(42)
```

</details>

#### returns a boolean-shaped native availability value

- returns a boolean-shaped native availability value
- Verify: returns a boolean-shaped native availability value
   - Expected: available == true or available == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns a boolean-shaped native availability value")
step("Verify: returns a boolean-shaped native availability value")
val available = is_native_available()

expect(available == true or available == false).to_equal(true)
```

</details>

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
- `REQ-COMP-NATIVE-BRIDGE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fcfeb9e13919fe4a2f47c58a7f901cc9590eeaeddfcd0e28c8633528dd753ce7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fcfeb9e13919fe4a2f47c58a7f901cc9590eeaeddfcd0e28c8633528dd753ce7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fcfeb9e13919fe4a2f47c58a7f901cc9590eeaeddfcd0e28c8633528dd753ce7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/01_unit/compiler/backend/native_bridge_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/native_bridge_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=80 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/native_bridge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/native_bridge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/native_bridge_spec.spl:1:1: advice SSDOC-COV-001 [coverage] (-20): the authored requirement defines adverse behavior but no adverse scenario is named
  why: Specifications should explain behavior outside the happy path.
  improve: Add adverse-path scenarios required by the source, or record a reasoned suppression.
test/01_unit/compiler/backend/native_bridge_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/native_bridge_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds compile result values for success and failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/native_bridge_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves execution result fields on hand-built values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/native_bridge_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a boolean-shaped native availability value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
