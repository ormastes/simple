# Wine Kernel32 File Metadata Specification

> Tests covering Wine KERNEL32 file metadata bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 File Metadata Specification

## Scenarios

### Wine KERNEL32 file metadata bridge

#### executes standalone GetFileAttributesW for files and directories

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes standalone GetFileAttributesW for files and directories
   - Expected: file_attrs.ok is true
   - Expected: file_attrs.attributes equals `0x80`
   - Expected: file_attrs.operations equals `GetFileAttributesW`
   - Expected: dir_attrs.ok is true
   - Expected: dir_attrs.attributes equals `0x10`
   - Expected: dir_attrs.operations equals `GetFileAttributesW`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("executes standalone GetFileAttributesW for files and directories")
val file_attrs = wine_kernel32_execute_file_attributes(["GetFileAttributesW"], _table_with_file(), "C:\\hello.txt")
expect(file_attrs.ok).to_equal(true)
expect(file_attrs.attributes).to_equal(0x80)
expect(file_attrs.operations).to_equal("GetFileAttributesW")

val dir_attrs = wine_kernel32_execute_file_attributes(["GetFileAttributesW"], _table_with_directory(), "C:\\TempDir")
expect(dir_attrs.ok).to_equal(true)
expect(dir_attrs.attributes).to_equal(0x10)
expect(dir_attrs.operations).to_equal("GetFileAttributesW")
```

</details>

#### executes a bounded attributes, open, size, information, seek, and close sequence

- executes a bounded attributes, open, size, information, seek, and close sequence
   - Expected: result.ok is true
   - Expected: result.handle equals `0x40`
   - Expected: result.attributes equals `0x80`
   - Expected: result.size equals `10`
   - Expected: result.information equals `0x100000 + 10`
   - Expected: result.pointer equals `6`
   - Expected: result.operations equals `GetFileAttributesW CreateFileW GetFileSize GetFileInformationByHandle SetFile... (full value in folded executable source)`
   - Expected: wine_nt_file_read(result.table, result.handle, 1).state equals `invalid-handle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("executes a bounded attributes, open, size, information, seek, and close sequence")
val result = wine_kernel32_execute_file_metadata(
    ["GetFileAttributesW", "CreateFileW", "GetFileSize", "GetFileInformationByHandle", "SetFilePointer", "CloseHandle"],
    _table_with_file(),
    "C:\\hello.txt",
    6
)

expect(result.ok).to_equal(true)
expect(result.handle).to_equal(0x40)
expect(result.attributes).to_equal(0x80)
expect(result.size).to_equal(10)
expect(result.information).to_equal(0x100000 + 10)
expect(result.pointer).to_equal(6)
expect(result.operations).to_equal("GetFileAttributesW CreateFileW GetFileSize GetFileInformationByHandle SetFilePointer CloseHandle")
expect(wine_nt_file_read(result.table, result.handle, 1).state).to_equal("invalid-handle")
```

</details>

#### keeps file metadata dispatch ordered and bounded

- keeps file metadata dispatch ordered and bounded
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-file-metadata-sequence-expected:GetFileAttributesW`
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`
   - Expected: attributes_extra.ok is false
   - Expected: attributes_extra.error equals `kernel32-file-metadata-sequence-count-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps file metadata dispatch ordered and bounded")
val out_of_order = wine_kernel32_execute_file_metadata(
    ["CreateFileW", "GetFileAttributesW", "GetFileSize", "GetFileInformationByHandle", "SetFilePointer", "CloseHandle"],
    _table_with_file(),
    "C:\\hello.txt",
    6
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-file-metadata-sequence-expected:GetFileAttributesW")

val wrong_family = wine_kernel32_execute_file_metadata(
    ["GetFileAttributesW", "CreateFileW", "GetFileSize", "GetFileInformationByHandle", "HeapAlloc", "CloseHandle"],
    _table_with_file(),
    "C:\\hello.txt",
    6
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")

val attributes_extra = wine_kernel32_execute_file_attributes(["GetFileAttributesW", "CloseHandle"], _table_with_file(), "C:\\hello.txt")
expect(attributes_extra.ok).to_equal(false)
expect(attributes_extra.error).to_equal("kernel32-file-metadata-sequence-count-mismatch")
```

</details>

#### propagates metadata and pointer failures

- propagates metadata and pointer failures
   - Expected: missing.ok is false
   - Expected: missing.error equals `GetFileAttributesW:file-not-found`
   - Expected: missing_attributes.ok is false
   - Expected: missing_attributes.error equals `GetFileAttributesW:file-not-found`
   - Expected: past_eof.ok is false
   - Expected: past_eof.error equals `SetFilePointer:file-pointer-past-eof`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("propagates metadata and pointer failures")
val missing = wine_kernel32_execute_file_metadata(
    ["GetFileAttributesW", "CreateFileW", "GetFileSize", "GetFileInformationByHandle", "SetFilePointer", "CloseHandle"],
    _table_with_file(),
    "C:\\missing.txt",
    0
)
expect(missing.ok).to_equal(false)
expect(missing.error).to_equal("GetFileAttributesW:file-not-found")

val missing_attributes = wine_kernel32_execute_file_attributes(["GetFileAttributesW"], _table_with_file(), "C:\\missing.txt")
expect(missing_attributes.ok).to_equal(false)
expect(missing_attributes.error).to_equal("GetFileAttributesW:file-not-found")

val past_eof = wine_kernel32_execute_file_metadata(
    ["GetFileAttributesW", "CreateFileW", "GetFileSize", "GetFileInformationByHandle", "SetFilePointer", "CloseHandle"],
    _table_with_file(),
    "C:\\hello.txt",
    99
)
expect(past_eof.ok).to_equal(false)
expect(past_eof.error).to_equal("SetFilePointer:file-pointer-past-eof")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_file_metadata_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine KERNEL32 file metadata bridge.
- Wine KERNEL32 file metadata bridge

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e50af3d402b865acf9fe39dcdae1fb1b190212bf830277360c19cf9f914556b6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e50af3d402b865acf9fe39dcdae1fb1b190212bf830277360c19cf9f914556b6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e50af3d402b865acf9fe39dcdae1fb1b190212bf830277360c19cf9f914556b6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/wine_kernel32_file_metadata_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_kernel32_file_metadata_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_kernel32_file_metadata_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_kernel32_file_metadata_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_kernel32_file_metadata_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_kernel32_file_metadata_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes standalone GetFileAttributesW for files and directories' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_kernel32_file_metadata_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes a bounded attributes, open, size, information, seek, and close sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_kernel32_file_metadata_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps file metadata dispatch ordered and bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
