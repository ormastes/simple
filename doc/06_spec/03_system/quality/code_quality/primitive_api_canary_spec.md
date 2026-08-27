# Primitive API Canary Spec — Wrapper-Type Shape Changes

> Canary specs that lock in specific public functions will use proper wrapper types instead of bare primitives after Teams D and B fix their suppressions (Phase 1).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Primitive API Canary Spec — Wrapper-Type Shape Changes

Canary specs that lock in specific public functions will use proper wrapper types instead of bare primitives after Teams D and B fix their suppressions (Phase 1).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | fix-primitive-api-suppressions |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/quality/code_quality/primitive_api_canary_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Canary specs that lock in specific public functions will use proper wrapper
types instead of bare primitives after Teams D and B fix their suppressions
(Phase 1).

NOTE: These specs verify that the *wrapper-typed call compiles correctly*.
They cannot directly assert the absence of bare `i64`/`i32` in a signature —
that is a grep gate at phase 7-verify.  The specs WILL FAIL until the
relevant team lands the wrapper-type refactor.

Canary targets (from state.md Pre-Pass Types table, Team D scope):
1. `Trace32Client.trace_capture(duration_ms: i32)` → `DurationMs` wrapper
   File: `src/app/debug/remote/protocol/trace32.spl`
2. `backend_shell_tuple(command: text) -> (text, text, i64)` → `ExitCode` in return
   File: `src/compiler/70.backend/backend/io_compat.spl`
3. `is_valid_handle(handle: i64) -> bool` → `Handle` wrapper
   File: `src/app/io/sffi_common.spl`

## Scenarios

### AC-2/AC-4 canary: Trace32Client.trace_capture uses DurationMs

#### AC-2: trace_capture accepts DurationMs wrapper (not bare i32)

- AC-2: trace_capture accepts DurationMs wrapper (not bare i32)
   - Expected: result.is_ok() or result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: trace_capture accepts DurationMs wrapper (not bare i32)")
val duration = DurationMs(value: 100)
val client = Trace32Client(
    host: "127.0.0.1",
    port: 20000,
    t32rem_path: "/bin/false",
    backend: "remote_cmd",
    connected: false,
    program: "",
    bp_counter: 0
)
val result = client.trace_capture(duration_ms: duration)
expect(result.is_ok() or result.is_err()).to_equal(true)
```

</details>

### AC-3 canary: backend_shell_tuple returns ExitCode

#### AC-3: backend_shell_tuple exit-code slot is ExitCode wrapper

- AC-3: backend_shell_tuple exit-code slot is ExitCode wrapper
   - Expected: exit_code.value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: backend_shell_tuple exit-code slot is ExitCode wrapper")
val result = backend_shell_tuple("echo hello")
val exit_code = result.2
val wrapper: ExitCode = exit_code
expect(exit_code.value).to_equal(0)
```

</details>

### AC-4 canary: sffi_common.is_valid_handle uses Handle

#### AC-4: is_valid_handle accepts Handle wrapper (not bare i64)

- AC-4: is_valid_handle accepts Handle wrapper (not bare i64)
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-4: is_valid_handle accepts Handle wrapper (not bare i64)")
val h = Handle(value: -1)
val valid = is_valid_handle(handle: h)
expect(valid).to_equal(true)
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `73bb10e4182ab182a96187a8366f0de754f93ff2c0e84f0042465ce3ed742209`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `73bb10e4182ab182a96187a8366f0de754f93ff2c0e84f0042465ce3ed742209`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `73bb10e4182ab182a96187a8366f0de754f93ff2c0e84f0042465ce3ed742209`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/quality/code_quality/primitive_api_canary_spec.spl
mirror: doc/06_spec/03_system/quality/code_quality/primitive_api_canary_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/quality/code_quality/primitive_api_canary_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/quality/code_quality/primitive_api_canary_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/quality/code_quality/primitive_api_canary_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/quality/code_quality/primitive_api_canary_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: trace_capture accepts DurationMs wrapper (not bare i32)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/primitive_api_canary_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: backend_shell_tuple exit-code slot is ExitCode wrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/primitive_api_canary_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: is_valid_handle accepts Handle wrapper (not bare i64)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
