# Wine Process Session Known Console Dispatch Specification

> Tests covering Wine process session known-console dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Known Console Dispatch Specification

## Scenarios

### Wine process session known-console dispatch

#### plans bounded known-console dispatch after CPU preflight

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- plans bounded known-console dispatch after CPU preflight
   - Expected: result.ok is true
   - Expected: result.command equals `game.exe`
   - Expected: result.instruction_sequence equals `xor-rcx-rcx call-rip-indirect lea-rdx-rip-rel32 call-rip-indirect xor-ecx-ecx... (full value in folded executable source)`
   - Expected: result.instruction_count equals `6`
   - Expected: result.call_sequence equals `GetStdHandle WriteFile ExitProcess`
   - Expected: result.call_count equals `3`
   - Expected: result.status equals `dispatch-planned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("plans bounded known-console dispatch after CPU preflight")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_known_console_dispatch(plan, wine_known_hello_exe_fixture_bytes(), 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()))
expect(result.ok).to_equal(true)
expect(result.command).to_equal("game.exe")
expect(result.instruction_sequence).to_equal("xor-rcx-rcx call-rip-indirect lea-rdx-rip-rel32 call-rip-indirect xor-ecx-ecx call-rip-indirect")
expect(result.instruction_count).to_equal(6)
expect(result.call_sequence).to_equal("GetStdHandle WriteFile ExitProcess")
expect(result.call_count).to_equal(3)
expect(result.status).to_equal("dispatch-planned")
```

</details>

#### plans known-console dispatch only after PEB/TEB VM byte-write readback

- plans known-console dispatch only after PEB/TEB VM byte-write readback
   - Expected: result.ok is true
   - Expected: result.instruction_count equals `6`
   - Expected: result.call_sequence equals `GetStdHandle WriteFile ExitProcess`
   - Expected: result.call_count equals `3`
   - Expected: result.status equals `dispatch-planned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("plans known-console dispatch only after PEB/TEB VM byte-write readback")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_process_plan_known_console_dispatch_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()), vm_writes)

expect(result.ok).to_equal(true)
expect(result.instruction_count).to_equal(6)
expect(result.call_sequence).to_equal("GetStdHandle WriteFile ExitProcess")
expect(result.call_count).to_equal(3)
expect(result.status).to_equal("dispatch-planned")
```

</details>

#### blocks known-console dispatch when PEB/TEB VM byte writes are not ready

- blocks known-console dispatch when PEB/TEB VM byte writes are not ready
   - Expected: result.ok is false
   - Expected: result.error equals `peb-teb-vm-write:vm-write:NtTib.StackBase:page-fault-unmapped`
   - Expected: result.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks known-console dispatch when PEB/TEB VM byte writes are not ready")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(wine_vm_process_space_new(10, 30, "pid fs ipc net capability"), bytes)
val result = wine_process_plan_known_console_dispatch_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()), vm_writes)

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
| Source | `test/unit/lib/common/wine_process_session_known_console_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine process session known-console dispatch.
- Wine process session known-console dispatch

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0c28215ac370c0d52cba477aecd641c7e58ad9ac5944b97cb15fc0799e562fbe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0c28215ac370c0d52cba477aecd641c7e58ad9ac5944b97cb15fc0799e562fbe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0c28215ac370c0d52cba477aecd641c7e58ad9ac5944b97cb15fc0799e562fbe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/wine_process_session_known_console_dispatch_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_process_session_known_console_dispatch_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_process_session_known_console_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_process_session_known_console_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_process_session_known_console_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_process_session_known_console_dispatch_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'plans bounded known-console dispatch after CPU preflight' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_process_session_known_console_dispatch_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'plans known-console dispatch only after PEB/TEB VM byte-write readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_process_session_known_console_dispatch_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks known-console dispatch when PEB/TEB VM byte writes are not ready' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
