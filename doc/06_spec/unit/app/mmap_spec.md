# Mmap Specification

> Tests covering MappedFile.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mmap Specification

## Scenarios

### MappedFile

#### struct construction

#### creates a valid MappedFile

- creates a valid MappedFile
   - Expected: mf.is_valid() is true
   - Expected: mf.file_size() equals `4096`
   - Expected: mf.path equals `/tmp/test.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a valid MappedFile")
val mf = MappedFile(address: 12345, size: 4096, path: "/tmp/test.txt")
expect(mf.is_valid()).to_equal(true)
expect(mf.file_size()).to_equal(4096)
expect(mf.path).to_equal("/tmp/test.txt")
```

</details>

#### zero address is invalid

- zero address is invalid
   - Expected: mf.is_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero address is invalid")
val mf = MappedFile(address: 0, size: 0, path: "")
expect(mf.is_valid()).to_equal(false)
```

</details>

#### bounds checking

#### read_bytes rejects negative offset

- read_bytes rejects negative offset
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read_bytes rejects negative offset")
val mf = MappedFile(address: 1000, size: 100, path: "test")
val result = mf.read_bytes(-1, 10)
expect(result.is_err()).to_equal(true)
```

</details>

#### read_bytes rejects negative length

- read_bytes rejects negative length
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read_bytes rejects negative length")
val mf = MappedFile(address: 1000, size: 100, path: "test")
val result = mf.read_bytes(0, -5)
expect(result.is_err()).to_equal(true)
```

</details>

#### read_bytes rejects read past end

- read_bytes rejects read past end
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read_bytes rejects read past end")
val mf = MappedFile(address: 1000, size: 100, path: "test")
val result = mf.read_bytes(90, 20)
expect(result.is_err()).to_equal(true)
```

</details>

#### read_string rejects negative offset

- read_string rejects negative offset
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read_string rejects negative offset")
val mf = MappedFile(address: 1000, size: 100, path: "test")
val result = mf.read_string(-1, 10)
expect(result.is_err()).to_equal(true)
```

</details>

#### read_string rejects offset past end

- read_string rejects offset past end
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read_string rejects offset past end")
val mf = MappedFile(address: 1000, size: 100, path: "test")
val result = mf.read_string(200, 10)
expect(result.is_err()).to_equal(true)
```

</details>

#### close

#### invalidates mapping after close

- invalidates mapping after close
   - Expected: mf.is_valid() is true
   - Expected: mf.is_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalidates mapping after close")
var mf = MappedFile(address: 1000, size: 100, path: "test")
expect(mf.is_valid()).to_equal(true)
# Note: close() calls rt_munmap which isn't available in interpreter
# We test the address zeroing logic by setting directly
mf.address = 0
mf.size = 0
expect(mf.is_valid()).to_equal(false)
```

</details>

#### open error handling

#### returns error for non-existent file

- returns error for non-existent file
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for non-existent file")
val result = MappedFile.open("/tmp/simple_mmap_nonexistent_file_12345.txt")
expect(result.is_err()).to_equal(true)
val err = result.unwrap_err()
expect(err).to_contain("not found")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mmap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MappedFile.
- MappedFile

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

- Canonical SPipe generation for source `7da2ca6221b65a3cedb95c60172e4e129957c7fe6be4fa1b5549ff3939210977`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7da2ca6221b65a3cedb95c60172e4e129957c7fe6be4fa1b5549ff3939210977`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7da2ca6221b65a3cedb95c60172e4e129957c7fe6be4fa1b5549ff3939210977`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/mmap_spec.spl
mirror: doc/06_spec/unit/app/mmap_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mmap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mmap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mmap_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mmap_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a valid MappedFile' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mmap_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'zero address is invalid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mmap_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'read_bytes rejects negative offset' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
