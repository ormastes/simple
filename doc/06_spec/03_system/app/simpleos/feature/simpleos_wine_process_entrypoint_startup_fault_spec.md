# Simpleos Wine Process Entrypoint Startup Fault Specification

> Tests covering REQ-045: process imported entrypoint startup fault rollback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Entrypoint Startup Fault Specification

## Scenarios

### REQ-045: process imported entrypoint startup fault rollback

#### records SEH rollback after import-bound entrypoint handoff while keeping PE code non-executing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-045
```

</details>

#### requires PEB/TEB VM byte-write readback before import-bound entrypoint rollback

- requires PEB/TEB VM byte-write readback before import-bound entrypoint rollback
   - Expected: result.ok is true
   - Expected: result.status equals `imported-entrypoint-startup-fault-rollback-recorded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires PEB/TEB VM byte-write readback before import-bound entrypoint rollback")
val fault = WineVmFault(process_id: 77, thread_id: 12, address: 0x402000, access: "execute", policy: "deliver-seh")
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_process_record_imported_entrypoint_handoff_startup_fault_with_peb_teb_vm_writes(_ready_handoff(), fault, vm_writes)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("imported-entrypoint-startup-fault-rollback-recorded")
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("VMWriteReadback:PEBTEBLayoutBytes")
expect(result.evidence).to_contain("no-arbitrary-execution")
```

</details>

#### blocks import-bound entrypoint rollback without carrying mapped state when PEB/TEB VM byte writes fail

- blocks import-bound entrypoint rollback without carrying mapped state when PEB/TEB VM byte writes fail
   - Expected: result.ok is false
   - Expected: result.error equals `imported-entrypoint-handoff:peb-teb-vm-write:vm-write:NtTib.StackBase:page-fa... (full value in folded executable source)`
   - Expected: result.mapped_base equals `0`
   - Expected: result.mapped_size equals `0`
   - Expected: result.entry_address equals `0`
   - Expected: result.module_count equals `0`
   - Expected: result.rollback_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("blocks import-bound entrypoint rollback without carrying mapped state when PEB/TEB VM byte writes fail")
val fault = WineVmFault(process_id: 77, thread_id: 12, address: 0x402000, access: "execute", policy: "deliver-seh")
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(wine_vm_process_space_new(10, 30, "pid fs ipc net capability"), bytes)
val result = wine_process_record_imported_entrypoint_handoff_startup_fault_with_peb_teb_vm_writes(_ready_handoff(), fault, vm_writes)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("imported-entrypoint-handoff:peb-teb-vm-write:vm-write:NtTib.StackBase:page-fault-unmapped")
expect(result.mapped_base).to_equal(0)
expect(result.mapped_size).to_equal(0)
expect(result.entry_address).to_equal(0)
expect(result.module_count).to_equal(0)
expect(result.rollback_count).to_equal(0)
expect(result.evidence).to_contain("imported-entrypoint-handoff-blocked")
expect(result.evidence).to_contain("process-entrypoint-startup-fault-blocked")
expect(result.evidence).to_contain("no-arbitrary-execution")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_entrypoint_startup_fault_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering REQ-045: process imported entrypoint startup fault rollback.
- REQ-045: process imported entrypoint startup fault rollback

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
- `REQ-045`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1348104907cca02cb2d62e3a3eda89d2442aa1fa5bed86dcbc4b9a771dd5204b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1348104907cca02cb2d62e3a3eda89d2442aa1fa5bed86dcbc4b9a771dd5204b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1348104907cca02cb2d62e3a3eda89d2442aa1fa5bed86dcbc4b9a771dd5204b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/app/simpleos/feature/simpleos_wine_process_entrypoint_startup_fault_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_entrypoint_startup_fault_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_entrypoint_startup_fault_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_entrypoint_startup_fault_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos/feature/simpleos_wine_process_entrypoint_startup_fault_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simpleos/feature/simpleos_wine_process_entrypoint_startup_fault_spec.spl:91:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'records SEH rollback after import-bound entrypoint handoff while keeping PE code non-executing' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/simpleos/feature/simpleos_wine_process_entrypoint_startup_fault_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires PEB/TEB VM byte-write readback before import-bound entrypoint rollback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_wine_process_entrypoint_startup_fault_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks import-bound entrypoint rollback without carrying mapped state when PEB/TEB VM byte writes fail' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
