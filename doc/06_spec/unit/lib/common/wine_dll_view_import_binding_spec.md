# Wine Dll View Import Binding Specification

> Tests covering wine dll view import binding.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Dll View Import Binding Specification

## Scenarios

### wine dll view import binding

#### patches modeled import addresses through a retained relocated DLL view

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- patches modeled import addresses through a retained relocated DLL view
   - Expected: result.ok is true
   - Expected: result.status equals `dll-view-imports-bound`
   - Expected: result.mapped_base equals `0x500000`
   - Expected: result.module_count equals `1`
   - Expected: result.resolved_count equals `1`
   - Expected: result.patched_count equals `1`
   - Expected: result.first_iat_rva equals `0x2080`
   - Expected: _read_u64_le(result.patched_image, pe_rva_to_file_offset(result.patched_image, 0x2080)) equals `0x120006`
   - Expected: _read_u64_le(result.patched_image, pe_rva_to_file_offset(result.patched_image, 0x2100)) equals `0x501234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("patches modeled import addresses through a retained relocated DLL view")
val data = _dll_with_import_and_relocation()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val result = wine_dll_bind_file_view_imports("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4)
expect(result.ok).to_equal(true)
expect(result.status).to_equal("dll-view-imports-bound")
expect(result.mapped_base).to_equal(0x500000)
expect(result.module_count).to_equal(1)
expect(result.resolved_count).to_equal(1)
expect(result.patched_count).to_equal(1)
expect(result.first_iat_rva).to_equal(0x2080)
expect(_read_u64_le(result.patched_image, pe_rva_to_file_offset(result.patched_image, 0x2080))).to_equal(0x120006)
expect(_read_u64_le(result.patched_image, pe_rva_to_file_offset(result.patched_image, 0x2100))).to_equal(0x501234)
expect(result.evidence).to_contain("dll-view-relocations-applied")
expect(result.evidence).to_contain("dll-import-thunk-bytes-written")
expect(result.evidence).to_contain("dll-view-rx-restored")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
```

</details>

#### rejects unsupported DLL imports before opening the import write window

- rejects unsupported DLL imports before opening the import write window
   - Expected: result.ok is false
   - Expected: result.error equals `unsupported-import-module:missing.dll`
   - Expected: result.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unsupported DLL imports before opening the import write window")
var data = _dll_with_import_and_relocation()
data = _put_ascii_z(data, 0x250, "missing.dll")
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val result = wine_dll_bind_file_view_imports("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("unsupported-import-module:missing.dll")
expect(result.evidence).to_contain("no-dll-iat-written")
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_dll_view_import_binding_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering wine dll view import binding.
- wine dll view import binding

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a8248324aaf7cf12c94aa903dc63c9a681d33b00e10f8e0b5259827ef2d4f1db`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a8248324aaf7cf12c94aa903dc63c9a681d33b00e10f8e0b5259827ef2d4f1db`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a8248324aaf7cf12c94aa903dc63c9a681d33b00e10f8e0b5259827ef2d4f1db`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/wine_dll_view_import_binding_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_dll_view_import_binding_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_dll_view_import_binding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_dll_view_import_binding_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_dll_view_import_binding_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_dll_view_import_binding_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'patches modeled import addresses through a retained relocated DLL view' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_dll_view_import_binding_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unsupported DLL imports before opening the import write window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
