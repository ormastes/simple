# Process Spawn Path Specification

> Tests covering spawn_path marshaling, spawn_path API.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Process Spawn Path Specification

## Scenarios

### spawn_path marshaling

#### returns empty buffer for empty input

- returns empty buffer for empty input


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty buffer for empty input")
val buf = _make_empty_buf()
expect buf.len() == 0
```

</details>

#### marshals single string with correct total size

- marshals single string with correct total size


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marshals single string with correct total size")
val buf = _make_single_string_buf()
# "hello" = 5 bytes + 1 NUL + 1 offset (8 bytes) + NULL terminator (8 bytes)
# = 6 + 16 = 22
val expected = _expected_size(1, 5)
expect expected == 22
expect buf.len().to_u64() == expected
```

</details>

#### places NUL terminator after string bytes

- places NUL terminator after string bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("places NUL terminator after string bytes")
val buf = _make_single_string_buf()
# buf[0..4] = "hello", buf[5] = 0x00
expect buf[0] == 0x68u8  # 'h'
expect buf[1] == 0x65u8  # 'e'
expect buf[2] == 0x6Cu8  # 'l'
expect buf[3] == 0x6Cu8  # 'l'
expect buf[4] == 0x6Fu8  # 'o'
expect buf[5] == 0x00u8  # NUL
```

</details>

#### encodes offset 0 for first string in pointer table

- encodes offset 0 for first string in pointer table


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes offset 0 for first string in pointer table")
val buf = _make_single_string_buf()
# Offset table starts at byte 6 (after "hello\0")
# First offset = 0, little-endian u64
expect buf[6] == 0x00u8
expect buf[7] == 0x00u8
expect buf[8] == 0x00u8
expect buf[9] == 0x00u8
expect buf[10] == 0x00u8
expect buf[11] == 0x00u8
expect buf[12] == 0x00u8
expect buf[13] == 0x00u8
```

</details>

#### ends with 8-byte NULL terminator pointer

- ends with 8-byte NULL terminator pointer


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ends with 8-byte NULL terminator pointer")
val buf = _make_single_string_buf()
val n = buf.len()
# Last 8 bytes should all be zero
expect buf[n - 1] == 0x00u8
expect buf[n - 2] == 0x00u8
expect buf[n - 3] == 0x00u8
expect buf[n - 4] == 0x00u8
expect buf[n - 5] == 0x00u8
expect buf[n - 6] == 0x00u8
expect buf[n - 7] == 0x00u8
expect buf[n - 8] == 0x00u8
```

</details>

#### marshals two strings with correct total size

- marshals two strings with correct total size


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marshals two strings with correct total size")
val buf = _make_two_string_buf()
# "ab" (2+1) + "cde" (3+1) = 7 string bytes
# + 2 offsets (16) + NULL ptr (8) = 31
val expected = _expected_size(2, 5)
expect expected == 31
expect buf.len().to_u64() == expected
```

</details>

#### encodes second string offset correctly

- encodes second string offset correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes second string offset correctly")
val buf = _make_two_string_buf()
# String data: "ab\0cde\0" = 7 bytes
# Offset table starts at byte 7
# offset[0] = 0  (bytes 7..14)
# offset[1] = 3  (bytes 15..22) — "ab\0" is 3 bytes
expect buf[15] == 0x03u8  # offset = 3, low byte
expect buf[16] == 0x00u8
```

</details>

#### preserves string content for two-element vector

- preserves string content for two-element vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves string content for two-element vector")
val buf = _make_two_string_buf()
# "ab" at offset 0
expect buf[0] == 0x61u8  # 'a'
expect buf[1] == 0x62u8  # 'b'
expect buf[2] == 0x00u8  # NUL
# "cde" at offset 3
expect buf[3] == 0x63u8  # 'c'
expect buf[4] == 0x64u8  # 'd'
expect buf[5] == 0x65u8  # 'e'
expect buf[6] == 0x00u8  # NUL
```

</details>

### spawn_path API
_Verify spawn_path error handling, argv defaults, and type signatures._

#### returns Err(EINVAL) for empty path

- returns Err(EINVAL) for empty path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Err(EINVAL) for empty path")
val result = spawn_path("", [], [])
expect result.is_err() == true
expect result.unwrap_err() == 22
```

</details>

#### returns Err(EINVAL) for empty path with argv

- returns Err(EINVAL) for empty path with argv


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Err(EINVAL) for empty path with argv")
val result = spawn_path("", ["arg0"], ["HOME=/home"])
expect result.is_err() == true
expect result.unwrap_err() == 22
```

</details>

#### sosix_marshal_string_vector accepts [text] and returns [u8]

- sosix_marshal_string_vector accepts [text] and returns [u8]


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sosix_marshal_string_vector accepts [text] and returns [u8]")
val input: [text] = ["test"]
val result: [u8] = sosix_marshal_string_vector(input)
expect result.len() > 0
```

</details>

#### sosix_marshal_string_vector_size returns u64

- sosix_marshal_string_vector_size returns u64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sosix_marshal_string_vector_size returns u64")
val size: u64 = sosix_marshal_string_vector_size(2, 10)
# total_bytes(10) + count(2) + (count+1)*8 = 10 + 2 + 24 = 36
expect size == 36
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/userlib/process_spawn_path_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering spawn_path marshaling, spawn_path API.
- spawn_path marshaling
- spawn_path API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `2be9c1eacc76c9520908e0dc9ded52be7e3dd104218a33e53e5bf92afaff5f8f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2be9c1eacc76c9520908e0dc9ded52be7e3dd104218a33e53e5bf92afaff5f8f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2be9c1eacc76c9520908e0dc9ded52be7e3dd104218a33e53e5bf92afaff5f8f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/userlib/process_spawn_path_spec.spl
mirror: doc/06_spec/unit/os/userlib/process_spawn_path_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/userlib/process_spawn_path_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/userlib/process_spawn_path_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/userlib/process_spawn_path_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty buffer for empty input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/userlib/process_spawn_path_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marshals single string with correct total size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/userlib/process_spawn_path_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'places NUL terminator after string bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
