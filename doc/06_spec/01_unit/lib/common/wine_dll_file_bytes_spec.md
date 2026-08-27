# Wine Dll File Bytes Specification

> Tests covering wine dll file bytes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Dll File Bytes Specification

## Scenarios

### wine dll file bytes

#### validates supplied file-backed PE DLL bytes before persistent mapping

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- validates supplied file-backed PE DLL bytes before persistent mapping
   - Expected: result.ok is true
   - Expected: result.dll_name equals `kernel32.dll`
   - Expected: result.selected_path equals `\\KnownDlls\\kernel32.dll`
   - Expected: result.byte_count equals `1024`
   - Expected: result.image_size equals `0x5000`
   - Expected: result.entrypoint_rva equals `0x1200`
   - Expected: result.status equals `dll-file-bytes-validated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("validates supplied file-backed PE DLL bytes before persistent mapping")
val result = wine_dll_validate_file_bytes("kernel32.dll", "\\KnownDlls\\kernel32.dll", _minimal_dll_bytes())
expect(result.ok).to_equal(true)
expect(result.dll_name).to_equal("kernel32.dll")
expect(result.selected_path).to_equal("\\KnownDlls\\kernel32.dll")
expect(result.byte_count).to_equal(1024)
expect(result.image_size).to_equal(0x5000)
expect(result.entrypoint_rva).to_equal(0x1200)
expect(result.status).to_equal("dll-file-bytes-validated")
expect(result.evidence).to_contain("file-backed-dll-bytes")
expect(result.evidence).to_contain("pe-dll-characteristic")
expect(result.evidence).to_contain("no-persistent-dll-view")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
```

</details>

#### rejects non-DLL PE images and malformed byte buffers

- rejects non-DLL PE images and malformed byte buffers
   - Expected: non_dll.ok is false
   - Expected: non_dll.error equals `pe-image-is-not-dll`
   - Expected: bad.error equals `dll-bytes-too-small`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects non-DLL PE images and malformed byte buffers")
var exe = _minimal_dll_bytes()
exe = _put_u16_le(exe, 0x96, 0x0022)
val non_dll = wine_dll_validate_file_bytes("kernel32.dll", "\\KnownDlls\\kernel32.dll", exe)
expect(non_dll.ok).to_equal(false)
expect(non_dll.error).to_equal("pe-image-is-not-dll")
val bad = wine_dll_validate_file_bytes("kernel32.dll", "\\KnownDlls\\kernel32.dll", [1, 2, 3])
expect(bad.error).to_equal("dll-bytes-too-small")
```

</details>

#### requires selected path and DLL entrypoint metadata

- requires selected path and DLL entrypoint metadata
   - Expected: missing_path.error equals `missing-selected-path`
   - Expected: result.error equals `missing-dll-entrypoint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires selected path and DLL entrypoint metadata")
val missing_path = wine_dll_validate_file_bytes("kernel32.dll", "", _minimal_dll_bytes())
expect(missing_path.error).to_equal("missing-selected-path")
var missing_entry = _minimal_dll_bytes()
missing_entry = _put_u32_le(missing_entry, 0x98 + 0x10, 0)
val result = wine_dll_validate_file_bytes("kernel32.dll", "\\KnownDlls\\kernel32.dll", missing_entry)
expect(result.error).to_equal("missing-dll-entrypoint")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_dll_file_bytes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering wine dll file bytes.
- wine dll file bytes

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

- Canonical SPipe generation for source `8cdf62499664294fd4996d16350afa99e3160f35af53c8aa67afe4ca867fdfa8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8cdf62499664294fd4996d16350afa99e3160f35af53c8aa67afe4ca867fdfa8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8cdf62499664294fd4996d16350afa99e3160f35af53c8aa67afe4ca867fdfa8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/wine_dll_file_bytes_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_dll_file_bytes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_dll_file_bytes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_dll_file_bytes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_dll_file_bytes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_dll_file_bytes_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates supplied file-backed PE DLL bytes before persistent mapping' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_dll_file_bytes_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-DLL PE images and malformed byte buffers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_dll_file_bytes_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires selected path and DLL entrypoint metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
