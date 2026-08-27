# Simpleos Wine Process Vma Relocation Specification

> Tests covering SimpleOS Wine VMA relocation application, REQ-036: loader-owned relocation mutation through process VMA.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Vma Relocation Specification

## Scenarios

### SimpleOS Wine VMA relocation application

### REQ-036: loader-owned relocation mutation through process VMA

#### should apply a bounded relocation in the mapped process image without executing PE code

- should apply a bounded relocation in the mapped process image without executing PE code
   - Expected: result.ok is true
   - Expected: result.relocation_count equals `1`
   - Expected: result.target_rva equals `0x2018`
   - Expected: _read_u64_le(result.patched_image, target_offset) equals `0x502018`
   - Expected: result.status equals `loader-relocations-vma-applied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-036 REQ-SSPEC-SYSTEM
step("should apply a bounded relocation in the mapped process image without executing PE code")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val data = _known_hello_with_dir64_relocation()
val target_offset = pe_rva_to_file_offset(data, 0x2018)
val result = wine_process_apply_loader_relocations_in_vma(plan, data, 0x400000, 0x500000, "native-module-open tls-callback")
expect(result.ok).to_equal(true)
expect(result.relocation_count).to_equal(1)
expect(result.target_rva).to_equal(0x2018)
expect(_read_u64_le(result.patched_image, target_offset)).to_equal(0x502018)
expect(result.evidence).to_contain("loader-relocations-vma-applied")
expect(result.evidence).to_contain("process-vma-rx-restored")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("loader-relocations-vma-applied")
```

</details>

#### should require PEB/TEB VM byte-write readback before loader relocation mutation

- should require PEB/TEB VM byte-write readback before loader relocation mutation
   - Expected: result.ok is true
   - Expected: result.status equals `loader-relocations-vma-applied`
   - Expected: _read_u64_le(result.patched_image, target_offset) equals `0x502018`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require PEB/TEB VM byte-write readback before loader relocation mutation")
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
expect(result.evidence).to_contain("no-arbitrary-execution")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_vma_relocation_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine VMA relocation application, REQ-036: loader-owned relocation mutation through process VMA.
- SimpleOS Wine VMA relocation application
- REQ-036: loader-owned relocation mutation through process VMA

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
- `REQ-036`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d8f1252d35ec1ab553f86c1375e0eded1f102129be15bb822781934521df9217`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d8f1252d35ec1ab553f86c1375e0eded1f102129be15bb822781934521df9217`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d8f1252d35ec1ab553f86c1375e0eded1f102129be15bb822781934521df9217`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/simpleos/feature/simpleos_wine_process_vma_relocation_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_vma_relocation_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=90
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_vma_relocation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_vma_relocation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos/feature/simpleos_wine_process_vma_relocation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simpleos/feature/simpleos_wine_process_vma_relocation_spec.spl:80:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should apply a bounded relocation in the mapped process image without executing PE code' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_vma_relocation_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should apply a bounded relocation in the mapped process image without executing PE code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_wine_process_vma_relocation_spec.spl:96:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require PEB/TEB VM byte-write readback before loader relocation mutation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simpleos/feature/simpleos_wine_process_vma_relocation_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require PEB/TEB VM byte-write readback before loader relocation mutation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
