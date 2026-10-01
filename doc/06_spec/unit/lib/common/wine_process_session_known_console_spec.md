# Wine Process Session Known Console Specification

> Tests covering Wine process session known console execution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Known Console Specification

## Scenarios

### Wine process session known console execution

#### executes the bounded known-console process path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes the bounded known-console process path
   - Expected: result.ok is true
   - Expected: result.command equals `game.exe`
   - Expected: result.stdout equals `Hello from SimpleOS Wine\n`
   - Expected: result.exit_code equals `0`
   - Expected: result.status equals `known-console-executed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes the bounded known-console process path")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_execute_known_console(plan, wine_known_hello_exe_fixture_bytes(), 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()))
expect(result.ok).to_equal(true)
expect(result.command).to_equal("game.exe")
expect(result.stdout).to_equal("Hello from SimpleOS Wine\n")
expect(result.exit_code).to_equal(0)
expect(result.status).to_equal("known-console-executed")
```

</details>

#### blocks known-console execution before CPU preflight

- blocks known-console execution before CPU preflight
   - Expected: result.ok is false
   - Expected: result.error equals `missing-thread-context`
   - Expected: result.status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks known-console execution before CPU preflight")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_execute_known_console(plan, wine_known_hello_exe_fixture_bytes(), 8, "")
expect(result.ok).to_equal(false)
expect(result.error).to_equal("missing-thread-context")
expect(result.status).to_equal("blocked")
```

</details>

#### executes known-console path only after PEB/TEB VM byte-write readback

- executes known-console path only after PEB/TEB VM byte-write readback
   - Expected: result.ok is true
   - Expected: result.stdout equals `Hello from SimpleOS Wine\n`
   - Expected: result.exit_code equals `0`
   - Expected: result.status equals `known-console-executed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes known-console path only after PEB/TEB VM byte-write readback")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_process_execute_known_console_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()), vm_writes)
expect(result.ok).to_equal(true)
expect(result.stdout).to_equal("Hello from SimpleOS Wine\n")
expect(result.exit_code).to_equal(0)
expect(result.status).to_equal("known-console-executed")
```

</details>

#### blocks known-console execution when PEB/TEB VM byte writes are not ready

- blocks known-console execution when PEB/TEB VM byte writes are not ready
   - Expected: result.ok is false
   - Expected: result.error equals `peb-teb-vm-write:vm-write:NtTib.StackBase:page-fault-unmapped`
   - Expected: result.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks known-console execution when PEB/TEB VM byte writes are not ready")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(wine_vm_process_space_new(10, 30, "pid fs ipc net capability"), bytes)
val result = wine_process_execute_known_console_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()), vm_writes)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("peb-teb-vm-write:vm-write:NtTib.StackBase:page-fault-unmapped")
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_process_session_known_console_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine process session known console execution.
- Wine process session known console execution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c2f36758a9adaeb7f9e5dff416ad4831cea6d665c4282b7b7541c3c6c8a2b8b3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c2f36758a9adaeb7f9e5dff416ad4831cea6d665c4282b7b7541c3c6c8a2b8b3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c2f36758a9adaeb7f9e5dff416ad4831cea6d665c4282b7b7541c3c6c8a2b8b3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/wine_process_session_known_console_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_process_session_known_console_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_process_session_known_console_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_process_session_known_console_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_process_session_known_console_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_process_session_known_console_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes the bounded known-console process path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_process_session_known_console_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks known-console execution before CPU preflight' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_process_session_known_console_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes known-console path only after PEB/TEB VM byte-write readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
