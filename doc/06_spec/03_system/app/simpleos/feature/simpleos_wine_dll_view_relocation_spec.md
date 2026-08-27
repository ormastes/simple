# Simpleos Wine Dll View Relocation Specification

> Tests covering REQ-048 SimpleOS Wine DLL view relocations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Dll View Relocation Specification

## Scenarios

### REQ-048 SimpleOS Wine DLL view relocations

#### applies DLL view relocations without executing DLL startup code

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-048
```

</details>

#### applies DLL view relocations only after PEB/TEB VM byte-write readback

- applies DLL view relocations only after PEB/TEB VM byte-write readback
   - Expected: result.ok is true
   - Expected: result.status equals `dll-view-relocations-applied`
   - Expected: result.relocation_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies DLL view relocations only after PEB/TEB VM byte-write readback")
val data = _dll_with_relocation()
val files = [wine_dll_probe_file("\\KnownDlls\\kernel32.dll", data)]
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_dll_apply_file_view_relocations_with_peb_teb_vm_writes("kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], files, data, 0x400000, 0x500000, 91, 92, "pid fs ipc net capability", vm_writes)
expect(result.ok).to_equal(true)
expect(result.status).to_equal("dll-view-relocations-applied")
expect(result.relocation_count).to_equal(1)
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("VMWriteReadback:PEBTEBLayoutBytes")
expect(result.evidence).to_contain("dll-view-relocations-applied")
expect(result.evidence).to_contain("dll-view-write-window")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_dll_view_relocation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering REQ-048 SimpleOS Wine DLL view relocations.
- REQ-048 SimpleOS Wine DLL view relocations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-048`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5fc8d34eead0b9e44c9130d6ac6797163b2c412e0f06a9eda30c0fa405760e6c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5fc8d34eead0b9e44c9130d6ac6797163b2c412e0f06a9eda30c0fa405760e6c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5fc8d34eead0b9e44c9130d6ac6797163b2c412e0f06a9eda30c0fa405760e6c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/simpleos/feature/simpleos_wine_dll_view_relocation_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_dll_view_relocation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=90 oracle=90
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_dll_view_relocation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_dll_view_relocation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos/feature/simpleos_wine_dll_view_relocation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simpleos/feature/simpleos_wine_dll_view_relocation_spec.spl:92:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'applies DLL view relocations without executing DLL startup code' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/simpleos/feature/simpleos_wine_dll_view_relocation_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies DLL view relocations only after PEB/TEB VM byte-write readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
