# Native File and Directory Operations

> Tests native file and directory operations including file read/write, directory creation/listing, and path manipulation. Verifies that I/O operations correctly interact with the filesystem across supported platforms.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native File and Directory Operations

Tests native file and directory operations including file read/write, directory creation/listing, and path manipulation. Verifies that I/O operations correctly interact with the filesystem across supported platforms.

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | In Progress |
| Source | `test/03_system/feature/io/native_ops_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests native file and directory operations including file read/write, directory
creation/listing, and path manipulation. Verifies that I/O operations correctly
interact with the filesystem across supported platforms.

## Scenarios

### Native File Operations

#### creates and reads files

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates and reads files
   - Expected: read_content equals `content`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates and reads files")
val test_file = "/tmp/simple_native_file_test.txt"
val content = "Hello from native SFFI!"

check(file_write(test_file, content))
check(file_exists(test_file))

val read_content = file_read(test_file)
expect(read_content).to_equal(content)

check(file_delete(test_file))
check(not file_exists(test_file))
```

</details>

#### copies files

- copies files
   - Expected: dst_content equals `Copy test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("copies files")
val src = "/tmp/simple_copy_src.txt"
val dst = "/tmp/simple_copy_dst.txt"

file_write(src, "Copy test")
check(file_copy(src, dst))

val dst_content = file_read(dst)
expect(dst_content).to_equal("Copy test")

file_delete(src)
file_delete(dst)
```

</details>

#### gets file size

- gets file size
   - Expected: size equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets file size")
val test_file = "/tmp/simple_size_test.txt"
val content = "12345"

file_write(test_file, content)
val size = file_size_raw(test_file)
expect(size).to_equal(5)

file_delete(test_file)
```

</details>

### Native Directory Operations

#### creates directories

- creates directories


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates directories")
val test_dir = "/tmp/simple_native_dir_test"

check(dir_create(test_dir, false))
check(is_dir(test_dir))
check(dir_remove_all(test_dir) == 0)
```

</details>

#### creates nested directories recursively

- creates nested directories recursively


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates nested directories recursively")
val test_dir = "/tmp/simple_native_deep/sub1/sub2"

check(dir_create(test_dir, true))
check(is_dir(test_dir))
check(dir_remove_all("/tmp/simple_native_deep") == 0)
```

</details>

#### creates directory tree with dir_create_all

- creates directory tree with dir_create_all


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates directory tree with dir_create_all")
val test_dir = "/tmp/simple_create_all/a/b/c"

check(dir_create_all(test_dir))
check(is_dir(test_dir))
check(dir_remove_all("/tmp/simple_create_all") == 0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f6bac7d3f4080ac553f33faa18cffa8a416a78127da57542ef53af59fec6817a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f6bac7d3f4080ac553f33faa18cffa8a416a78127da57542ef53af59fec6817a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f6bac7d3f4080ac553f33faa18cffa8a416a78127da57542ef53af59fec6817a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/io/native_ops_spec.spl
mirror: doc/06_spec/03_system/feature/io/native_ops_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/io/native_ops_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/io/native_ops_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/io/native_ops_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/io/native_ops_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates and reads files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/io/native_ops_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'copies files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/io/native_ops_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gets file size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
