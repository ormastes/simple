# File System Specification

> Tests covering File System FFI Functions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# File System Specification

## Scenarios

### File System FFI Functions

#### file operations

#### should check if file exists

- should check if file exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should check if file exists")
# This test file should exist
val result = file.exist("simple/std_lib/test/unit/shell/file_system_spec.spl")
expect(result)
```

</details>

#### should return false for non-existent files

- should return false for non-existent files


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should return false for non-existent files")
val result = file.exist("/nonexistent/test/file.txt")
expect(not result)
```

</details>

#### should write and read text file

- should write and read text file


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should write and read text file")
val test_path = "/tmp/simple_test_file.txt"
val test_content = "Hello from Simple test!"

# Write to file
file.write_text(test_path, test_content)

# Read back
val read_content = file.read_text(test_path)
expect(read_content == test_content)

# Clean up
file.remove(test_path)
```

</details>

#### should append text to file

- should append text to file


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should append text to file")
val test_path = "/tmp/simple_test_append.txt"

# Write initial content
file.write_text(test_path, "Line 1\n")

# Append more content
file.append_text(test_path, "Line 2\n")

# Read all
val content = file.read_text(test_path)
expect(content == "Line 1\nLine 2\n")

# Clean up
file.remove(test_path)
```

</details>

#### should copy file

- should copy file


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should copy file")
val src_path = "/tmp/simple_test_src.txt"
val dest_path = "/tmp/simple_test_dest.txt"

# Write source file
file.write_text(src_path, "Copy me!")

# Copy it
file.copy(src_path, dest_path)

# Verify destination exists and has same content
expect(file.exist(dest_path))
val dest_content = file.read_text(dest_path)
expect(dest_content == "Copy me!")

# Clean up
file.remove(src_path)
file.remove(dest_path)
```

</details>

#### should rename/move file

- should rename/move file


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should rename/move file")
val src_path = "/tmp/simple_test_rename_src.txt"
val new_path = "/tmp/simple_test_rename_dest.txt"

# Write source file
file.write_text(src_path, "Move me!")

# Rename it
file.rename(src_path, new_path)

# Verify old doesn't exist, new does
expect(not file.exist(src_path))
expect(file.exist(new_path))
val content = file.read_text(new_path)
expect(content == "Move me!")

# Clean up
file.remove(new_path)
```

</details>

#### directory operations

#### should create and remove directory

- should create and remove directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create and remove directory")
val test_dir = "/tmp/simple_test_dir"

# Create directory
dir.create(test_dir)

# Verify it exists
expect(dir.exist(test_dir))

# Remove it
dir.remove(test_dir)

# Verify it's gone
expect(not dir.exist(test_dir))
```

</details>

#### should create recursive directory

- should create recursive directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create recursive directory")
val test_dir = "/tmp/simple_test/nested/deep"

# Create nested directories
dir.create_recursive(test_dir)

# Verify it exists
expect(dir.exist(test_dir))

# Clean up (recursive remove)
dir.remove_recursive("/tmp/simple_test")
```

</details>

#### should list directory entries

- should list directory entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should list directory entries")
val test_dir = "/tmp/simple_test_list"

# Create directory
dir.create(test_dir)

# Create some files
file.write_text("{test_dir}/file1.txt", "content1")
file.write_text("{test_dir}/file2.txt", "content2")
file.write_text("{test_dir}/file3.txt", "content3")

# List entries
val entries = dir.list(test_dir)

# Should have 3 entries
expect(entries.len() == 3)

# Clean up
file.remove("{test_dir}/file1.txt")
file.remove("{test_dir}/file2.txt")
file.remove("{test_dir}/file3.txt")
dir.remove(test_dir)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/std/shell/file_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering File System FFI Functions.
- File System FFI Functions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `343345b323dae1c2afca60b978a52712ed46c51fe8b532edbfec7cceb02f7fb4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `343345b323dae1c2afca60b978a52712ed46c51fe8b532edbfec7cceb02f7fb4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `343345b323dae1c2afca60b978a52712ed46c51fe8b532edbfec7cceb02f7fb4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/std/shell/file_system_spec.spl
mirror: doc/06_spec/unit/lib/std/shell/file_system_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/std/shell/file_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/std/shell/file_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/std/shell/file_system_spec.spl:15:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should check if file exists' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/shell/file_system_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should check if file exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/shell/file_system_spec.spl:22:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return false for non-existent files' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/shell/file_system_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should return false for non-existent files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/shell/file_system_spec.spl:28:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should write and read text file' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/shell/file_system_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should write and read text file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/shell/file_system_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should append text to file' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/shell/file_system_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should copy file' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/shell/file_system_spec.spl:83:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should rename/move file' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
