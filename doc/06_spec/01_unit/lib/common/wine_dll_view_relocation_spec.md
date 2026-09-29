# Wine Dll View Relocation Specification

> Tests covering wine dll view relocation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Dll View Relocation Specification

## Scenarios

### wine dll view relocation

#### applies a bounded DIR64 relocation through a retained DLL view write window

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- applies a bounded DIR64 relocation through a retained DLL view write window
   - Expected: result.ok is true
   - Expected: result.mapped_base equals `0x500000`
   - Expected: result.mapped_size equals `0x5000`
   - Expected: result.relocation_count equals `1`
   - Expected: result.target_rva equals `0x2100`
   - Expected: _read_u64_le(result.patched_image, pe_rva_to_file_offset(result.patched_image, 0x2100)) equals `0x501234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies a bounded DIR64 relocation through a retained DLL view write window")
val data = _dll_with_dir64_relocation()
val files = [wine_dll_probe_file("\\KnownDlls\\kernel32.dll", data)]
val result = wine_dll_apply_file_view_relocations("kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability")
expect(result.ok).to_equal(true)
expect(result.mapped_base).to_equal(0x500000)
expect(result.mapped_size).to_equal(0x5000)
expect(result.relocation_count).to_equal(1)
expect(result.target_rva).to_equal(0x2100)
expect(_read_u64_le(result.patched_image, pe_rva_to_file_offset(result.patched_image, 0x2100))).to_equal(0x501234)
expect(result.evidence).to_contain("file-backed-dll-view-persistent")
expect(result.evidence).to_contain("relocation-dir64")
expect(result.evidence).to_contain("dll-view-relocations-applied")
expect(result.evidence).to_contain("dll-view-rx-restored")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
```

</details>

#### applies retained DLL view relocations only after PEB/TEB VM byte-write readback

- applies retained DLL view relocations only after PEB/TEB VM byte-write readback
   - Expected: result.ok is true
   - Expected: result.status equals `dll-view-relocations-applied`
   - Expected: result.relocation_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies retained DLL view relocations only after PEB/TEB VM byte-write readback")
val data = _dll_with_dir64_relocation()
val files = [wine_dll_probe_file("\\KnownDlls\\kernel32.dll", data)]
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_dll_apply_file_view_relocations_with_peb_teb_vm_writes("kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", vm_writes)
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

#### rejects missing relocation directories before mutating the DLL image

- rejects missing relocation directories before mutating the DLL image
   - Expected: result.ok is false
   - Expected: result.error equals `relocation:missing-relocation-directory`
   - Expected: result.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects missing relocation directories before mutating the DLL image")
var data = _dll_with_dir64_relocation()
data = _put_u32_le(data, 0x98 + 0x70 + 40, 0)
data = _put_u32_le(data, 0x98 + 0x70 + 44, 0)
val files = [wine_dll_probe_file("\\KnownDlls\\kernel32.dll", data)]
val result = wine_dll_apply_file_view_relocations("kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability")
expect(result.ok).to_equal(false)
expect(result.error).to_equal("relocation:missing-relocation-directory")
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_dll_view_relocation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering wine dll view relocation.
- wine dll view relocation

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7beacacfaea0b67c973a7e34f84ad14934546eb533fee047b4fd77b4750b36e3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7beacacfaea0b67c973a7e34f84ad14934546eb533fee047b4fd77b4750b36e3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7beacacfaea0b67c973a7e34f84ad14934546eb533fee047b4fd77b4750b36e3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/wine_dll_view_relocation_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_dll_view_relocation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_dll_view_relocation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_dll_view_relocation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_dll_view_relocation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_dll_view_relocation_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies a bounded DIR64 relocation through a retained DLL view write window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_dll_view_relocation_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies retained DLL view relocations only after PEB/TEB VM byte-write readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_dll_view_relocation_spec.spl:145:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects missing relocation directories before mutating the DLL image' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
