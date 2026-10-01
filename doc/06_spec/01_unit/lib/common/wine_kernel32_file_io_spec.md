# Wine Kernel32 File Io Specification

> Tests covering Wine KERNEL32 file I/O bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 File Io Specification

## Scenarios

### Wine KERNEL32 file I/O bridge

#### executes a bounded CreateFileW, ReadFile, GetFileType, and CloseHandle sequence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes a bounded CreateFileW, ReadFile, GetFileType, and CloseHandle sequence
   - Expected: result.ok is true
   - Expected: result.handle equals `0x40`
   - Expected: result.data equals `hello`
   - Expected: result.bytes_read equals `5`
   - Expected: result.file_type equals `1`
   - Expected: result.operations equals `CreateFileW ReadFile GetFileType CloseHandle`
   - Expected: wine_nt_file_read(result.table, result.handle, 1).state equals `invalid-handle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("executes a bounded CreateFileW, ReadFile, GetFileType, and CloseHandle sequence")
val result = wine_kernel32_execute_file_io(["CreateFileW", "ReadFile", "GetFileType", "CloseHandle"], _table_with_file(), "C:\\hello.txt", 5)

expect(result.ok).to_equal(true)
expect(result.handle).to_equal(0x40)
expect(result.data).to_equal("hello")
expect(result.bytes_read).to_equal(5)
expect(result.file_type).to_equal(1)
expect(result.operations).to_equal("CreateFileW ReadFile GetFileType CloseHandle")
expect(wine_nt_file_read(result.table, result.handle, 1).state).to_equal("invalid-handle")
```

</details>

#### keeps file I/O dispatch ordered and bounded

- keeps file I/O dispatch ordered and bounded
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-file-io-sequence-expected:CreateFileW`
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapFree`
   - Expected: missing_file.ok is false
   - Expected: missing_file.error equals `CreateFileW:file-not-found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps file I/O dispatch ordered and bounded")
val out_of_order = wine_kernel32_execute_file_io(["ReadFile", "CreateFileW", "GetFileType", "CloseHandle"], _table_with_file(), "C:\\hello.txt", 5)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-file-io-sequence-expected:CreateFileW")

val wrong_family = wine_kernel32_execute_file_io(["CreateFileW", "ReadFile", "GetFileType", "HeapFree"], _table_with_file(), "C:\\hello.txt", 5)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapFree")

val missing_file = wine_kernel32_execute_file_io(["CreateFileW", "ReadFile", "GetFileType", "CloseHandle"], _table_with_file(), "C:\\missing.txt", 5)
expect(missing_file.ok).to_equal(false)
expect(missing_file.error).to_equal("CreateFileW:file-not-found")
```

</details>

#### propagates NT file-table readiness and read errors

- propagates NT file-table readiness and read errors
   - Expected: not_ready.ok is false
   - Expected: not_ready.error equals `CreateFileW:missing-api-fd-write`
   - Expected: invalid_read.ok is false
   - Expected: invalid_read.error equals `ReadFile:invalid-read-size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("propagates NT file-table readiness and read errors")
val blocked = wine_nt_file_table_new("fd-open fd-read", _all_async_features())
val not_ready = wine_kernel32_execute_file_io(["CreateFileW", "ReadFile", "GetFileType", "CloseHandle"], blocked, "C:\\hello.txt", 5)
expect(not_ready.ok).to_equal(false)
expect(not_ready.error).to_equal("CreateFileW:missing-api-fd-write")

val invalid_read = wine_kernel32_execute_file_io(["CreateFileW", "ReadFile", "GetFileType", "CloseHandle"], _table_with_file(), "C:\\hello.txt", -1)
expect(invalid_read.ok).to_equal(false)
expect(invalid_read.error).to_equal("ReadFile:invalid-read-size")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_file_io_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine KERNEL32 file I/O bridge.
- Wine KERNEL32 file I/O bridge

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

- Canonical SPipe generation for source `fd561c24078ebbdf54fc51e146dc7b305d531a28a41ae8777833bdfdac9981c5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd561c24078ebbdf54fc51e146dc7b305d531a28a41ae8777833bdfdac9981c5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd561c24078ebbdf54fc51e146dc7b305d531a28a41ae8777833bdfdac9981c5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/wine_kernel32_file_io_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_kernel32_file_io_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_kernel32_file_io_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_kernel32_file_io_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_kernel32_file_io_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_kernel32_file_io_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes a bounded CreateFileW, ReadFile, GetFileType, and CloseHandle sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_kernel32_file_io_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps file I/O dispatch ordered and bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_kernel32_file_io_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates NT file-table readiness and read errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
