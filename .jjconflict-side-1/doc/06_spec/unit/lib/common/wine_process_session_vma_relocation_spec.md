# Wine Process Session Vma Relocation Specification

> Tests covering Wine process session VMA relocation application.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Vma Relocation Specification

## Scenarios

### Wine process session VMA relocation application

#### applies a bounded DIR64 relocation through a process VMA write window

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- applies a bounded DIR64 relocation through a process VMA write window
   - Expected: result.ok is true
   - Expected: result.mapped_base equals `0x500000`
   - Expected: result.relocation_count equals `1`
   - Expected: result.target_rva equals `0x2018`
   - Expected: _read_u64_le(result.patched_image, target_offset) equals `0x502018`
   - Expected: result.status equals `loader-relocations-vma-applied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies a bounded DIR64 relocation through a process VMA write window")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val data = _known_hello_with_dir64_relocation()
val target_offset = pe_rva_to_file_offset(data, 0x2018)
val result = wine_process_apply_loader_relocations_in_vma(plan, data, 0x400000, 0x500000, "native-module-open tls-callback")
expect(result.ok).to_equal(true)
expect(result.mapped_base).to_equal(0x500000)
expect(result.relocation_count).to_equal(1)
expect(result.target_rva).to_equal(0x2018)
expect(_read_u64_le(result.patched_image, target_offset)).to_equal(0x502018)
expect(result.evidence).to_contain("relocation-dir64")
expect(result.evidence).to_contain("loader-relocations-vma-applied")
expect(result.evidence).to_contain("process-vma-write-enabled")
expect(result.evidence).to_contain("process-vma-rx-restored")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("loader-relocations-vma-applied")
```

</details>

#### applies loader relocations only after PEB/TEB VM byte-write readback

- applies loader relocations only after PEB/TEB VM byte-write readback
   - Expected: result.ok is true
   - Expected: result.status equals `loader-relocations-vma-applied`
   - Expected: _read_u64_le(result.patched_image, target_offset) equals `0x502018`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies loader relocations only after PEB/TEB VM byte-write readback")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val data = _known_hello_with_dir64_relocation()
val target_offset = pe_rva_to_file_offset(data, 0x2018)
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_process_apply_loader_relocations_in_vma_with_peb_teb_vm_writes(plan, data, 0x400000, 0x500000, "native-module-open tls-callback", vm_writes)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("loader-relocations-vma-applied")
expect(_read_u64_le(result.patched_image, target_offset)).to_equal(0x502018)
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("VMWriteReadback:PEBTEBLayoutBytes")
expect(result.evidence).to_contain("loader-relocations-vma-applied")
```

</details>

#### blocks loader relocations when PEB/TEB VM byte writes are not ready

- blocks loader relocations when PEB/TEB VM byte writes are not ready
   - Expected: result.ok is false
   - Expected: result.error equals `peb-teb-vm-write:vm-write:NtTib.StackBase:page-fault-unmapped`
   - Expected: result.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks loader relocations when PEB/TEB VM byte writes are not ready")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val data = _known_hello_with_dir64_relocation()
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(wine_vm_process_space_new(10, 30, "pid fs ipc net capability"), bytes)
val result = wine_process_apply_loader_relocations_in_vma_with_peb_teb_vm_writes(plan, data, 0x400000, 0x500000, "native-module-open tls-callback", vm_writes)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("peb-teb-vm-write:vm-write:NtTib.StackBase:page-fault-unmapped")
expect(result.status).to_equal("rejected")
expect(result.evidence).to_contain("full-image-handoff-blocked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_process_session_vma_relocation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine process session VMA relocation application.
- Wine process session VMA relocation application

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

- Canonical SPipe generation for source `4b2bdbda1c95e15e75d097827d49c7d96a359d9bb673a1d202829b0119acfcf2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4b2bdbda1c95e15e75d097827d49c7d96a359d9bb673a1d202829b0119acfcf2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4b2bdbda1c95e15e75d097827d49c7d96a359d9bb673a1d202829b0119acfcf2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/common/wine_process_session_vma_relocation_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_process_session_vma_relocation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_process_session_vma_relocation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_process_session_vma_relocation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_process_session_vma_relocation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_process_session_vma_relocation_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies a bounded DIR64 relocation through a process VMA write window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_process_session_vma_relocation_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies loader relocations only after PEB/TEB VM byte-write readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_process_session_vma_relocation_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks loader relocations when PEB/TEB VM byte writes are not ready' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
