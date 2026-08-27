# Simpleos Wine Known Console Execution Specification

> Tests covering SimpleOS Wine known-console execution, REQ-019: bounded known-console process execution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Known Console Execution Specification

## Scenarios

### SimpleOS Wine known-console execution

### REQ-019: bounded known-console process execution

#### should execute a decoded known-console process session

- should execute a decoded known-console process session
   - Expected: execution.ok is true
   - Expected: execution.stdout equals `Hello from SimpleOS Wine\n`
   - Expected: execution.exit_code equals `0`
   - Expected: execution.status equals `known-console-executed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-019
# @req REQ-SSPEC-SYSTEM
step("should execute a decoded known-console process session")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val execution = wine_process_execute_known_console(plan, wine_known_hello_exe_fixture_bytes(), 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()))
expect(execution.ok).to_equal(true)
expect(execution.stdout).to_equal("Hello from SimpleOS Wine\n")
expect(execution.exit_code).to_equal(0)
expect(execution.status).to_equal("known-console-executed")
```

</details>

#### should block known-console process execution before CPU preflight

- should block known-console process execution before CPU preflight
   - Expected: execution.ok is false
   - Expected: execution.error equals `missing-thread-context`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should block known-console process execution before CPU preflight")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val execution = wine_process_execute_known_console(plan, wine_known_hello_exe_fixture_bytes(), 8, "")
expect(execution.ok).to_equal(false)
expect(execution.error).to_equal("missing-thread-context")
```

</details>

#### should require PEB/TEB VM byte-write readback before known-console execution

- should require PEB/TEB VM byte-write readback before known-console execution
   - Expected: execution.ok is true
   - Expected: execution.stdout equals `Hello from SimpleOS Wine\n`
   - Expected: execution.exit_code equals `0`
   - Expected: execution.status equals `known-console-executed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require PEB/TEB VM byte-write readback before known-console execution")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val execution = wine_process_execute_known_console_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()), vm_writes)
expect(execution.ok).to_equal(true)
expect(execution.stdout).to_equal("Hello from SimpleOS Wine\n")
expect(execution.exit_code).to_equal(0)
expect(execution.status).to_equal("known-console-executed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/system/app/simpleos/feature/simpleos_wine_known_console_execution_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine known-console execution, REQ-019: bounded known-console process execution.
- SimpleOS Wine known-console execution
- REQ-019: bounded known-console process execution

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
- `REQ-019`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0cee567203bf1b9ce4a3261baa4578a54d81d6953bc505abcd962cc74ddab4ec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0cee567203bf1b9ce4a3261baa4578a54d81d6953bc505abcd962cc74ddab4ec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0cee567203bf1b9ce4a3261baa4578a54d81d6953bc505abcd962cc74ddab4ec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/system/app/simpleos/feature/simpleos_wine_known_console_execution_spec.spl
mirror: doc/06_spec/system/app/simpleos/feature/simpleos_wine_known_console_execution_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/app/simpleos/feature/simpleos_wine_known_console_execution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/simpleos/feature/simpleos_wine_known_console_execution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/simpleos/feature/simpleos_wine_known_console_execution_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/system/app/simpleos/feature/simpleos_wine_known_console_execution_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute a decoded known-console process session' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/simpleos/feature/simpleos_wine_known_console_execution_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should execute a decoded known-console process session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/simpleos/feature/simpleos_wine_known_console_execution_spec.spl:58:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should block known-console process execution before CPU preflight' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/simpleos/feature/simpleos_wine_known_console_execution_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should block known-console process execution before CPU preflight' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/simpleos/feature/simpleos_wine_known_console_execution_spec.spl:66:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require PEB/TEB VM byte-write readback before known-console execution' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/simpleos/feature/simpleos_wine_known_console_execution_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require PEB/TEB VM byte-write readback before known-console execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
