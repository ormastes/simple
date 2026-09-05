# Image Bounded File Reader Specification

> Tests covering Installer bounded file reader.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Image Bounded File Reader Specification

## Scenarios

### Installer bounded file reader

#### fails closed before allocating from a regular changeable host file

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fails closed before allocating from a regular changeable host file


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed before allocating from a regular changeable host file")
val dir = _reader_fixture_dir()
val path = "{dir}/payload.bin"
expect(file_write_bytes(path, [0u8, 1u8, 2u8, 255u8])).to_be(true)
val result = image_read_file_bounded_v1(path, 4, "test payload")
expect(result.is_err()).to_be(true)
if val Err(message) = result:
    expect(message).to_contain(IMAGE_BOUNDED_FILE_READER_UNAVAILABLE_V1)
```

</details>

#### rejects a symlink instead of following a changeable source name

- rejects a symlink instead of following a changeable source name
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a symlink instead of following a changeable source name")
val dir = _reader_fixture_dir()
val target = "{dir}/target.bin"
val link = "{dir}/link.bin"
expect(file_write_bytes(target, [7u8, 8u8])).to_be(true)
val (_out, _err, code) = process_run("/bin/ln", ["-s", "target.bin", link])
expect(code).to_equal(0)
val result = image_read_file_bounded_v1(link, 8, "test payload")
expect(result.is_err()).to_be(true)
if val Err(message) = result:
    expect(message).to_contain("symlink")
```

</details>

#### applies the same fail-closed owner boundary to installer text

- applies the same fail-closed owner boundary to installer text


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("applies the same fail-closed owner boundary to installer text")
val dir = _reader_fixture_dir()
val path = "{dir}/package.spk"
expect(file_write_bytes(path, [112u8, 107u8, 103u8])).to_be(true)
val result = image_read_text_bounded_v1(path, 8, "test package")
expect(result.is_err()).to_be(true)
if val Err(message) = result:
    expect(message).to_contain(IMAGE_BOUNDED_FILE_READER_UNAVAILABLE_V1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/installer/image_bounded_file_reader_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Installer bounded file reader.
- Installer bounded file reader

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `043ad2f897b6b7dbd10756692a6888a2edbacc64e69702e152723d686792fef4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `043ad2f897b6b7dbd10756692a6888a2edbacc64e69702e152723d686792fef4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `043ad2f897b6b7dbd10756692a6888a2edbacc64e69702e152723d686792fef4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/installer/image_bounded_file_reader_spec.spl
mirror: doc/06_spec/01_unit/os/installer/image_bounded_file_reader_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/installer/image_bounded_file_reader_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/installer/image_bounded_file_reader_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/installer/image_bounded_file_reader_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/installer/image_bounded_file_reader_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed before allocating from a regular changeable host file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/installer/image_bounded_file_reader_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a symlink instead of following a changeable source name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/installer/image_bounded_file_reader_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies the same fail-closed owner boundary to installer text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
