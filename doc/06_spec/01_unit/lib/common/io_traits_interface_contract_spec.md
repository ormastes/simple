# Io Traits Interface Contract Specification

> Tests covering sync I/O trait interface contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Io Traits Interface Contract Specification

## Scenarios

### sync I/O trait interface contract

#### implements byte and text read/write behavior

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- implements byte and text read/write behavior
   - Expected: stream.read_exact(2).unwrap() equals `[65u8, 66u8]`
   - Expected: stream.read_all().unwrap() equals `[67u8]`
   - Expected: stream.write([68u8]).unwrap() equals `1`
   - Expected: stream.read_text().unwrap() equals `안녕하세요`
   - Expected: stream.read_line().unwrap() equals `안녕하세요`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
# @req REQ-006
step("implements byte and text read/write behavior")
val stream = ContractMemoryStream.new([65u8, 66u8, 67u8], "ABC")
expect(stream.read_exact(2).unwrap()).to_equal([65u8, 66u8])
expect(stream.read_all().unwrap()).to_equal([67u8])
expect(stream.read_exact(1).is_err()).to_be(true)
expect(stream.read(-1).is_err()).to_be(true)
expect(stream.write([68u8]).unwrap()).to_equal(1)
expect(stream.write_all([69u8]).is_ok()).to_be(true)
expect(stream.write_text("안녕하세요").is_ok()).to_be(true)
expect(stream.read_text().unwrap()).to_equal("안녕하세요")
expect(stream.read_line().unwrap()).to_equal("안녕하세요")
expect(stream.flush().is_ok()).to_be(true)
```

</details>

#### implements all seek origins and rejects negative positions

- implements all seek origins and rejects negative positions
   - Expected: stream.seek(SeekFrom.Start(2)).unwrap() equals `2`
   - Expected: stream.seek(SeekFrom.Current(1)).unwrap() equals `3`
   - Expected: stream.seek(SeekFrom.End(-1)).unwrap() equals `3`
   - Expected: stream.position().unwrap() equals `3`
   - Expected: stream.position().unwrap() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
# @req REQ-007
step("implements all seek origins and rejects negative positions")
val stream = ContractMemoryStream.new([1u8, 2u8, 3u8, 4u8], "")
expect(stream.seek(SeekFrom.Start(2)).unwrap()).to_equal(2)
expect(stream.seek(SeekFrom.Current(1)).unwrap()).to_equal(3)
expect(stream.seek(SeekFrom.End(-1)).unwrap()).to_equal(3)
expect(stream.position().unwrap()).to_equal(3)
expect(stream.rewind().is_ok()).to_be(true)
expect(stream.position().unwrap()).to_equal(0)
expect(stream.seek(SeekFrom.Current(-1)).is_err()).to_be(true)
```

</details>

#### closes deterministically and rejects every post-close operation

- closes deterministically and rejects every post-close operation


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
# @req REQ-014
step("closes deterministically and rejects every post-close operation")
val stream = ContractMemoryStream.new([65u8], "A")
expect(stream.is_open()).to_be(true)
expect(stream.close().is_ok()).to_be(true)
expect(stream.is_open()).to_be(false)
expect(stream.read(1).is_err()).to_be(true)
expect(stream.read_text().is_err()).to_be(true)
expect(stream.write([66u8]).is_err()).to_be(true)
expect(stream.write_text("B").is_err()).to_be(true)
expect(stream.flush().is_err()).to_be(true)
expect(stream.seek(SeekFrom.Start(0)).is_err()).to_be(true)
expect(stream.position().is_err()).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/io_traits_interface_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sync I/O trait interface contract.
- sync I/O trait interface contract

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
- `REQ-006`
- `REQ-007`
- `REQ-014`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `68c1ecf8f0ff13e0bc3f2d2e5ae9928dd7710b6d64fa6652e694f46768c3e44c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `68c1ecf8f0ff13e0bc3f2d2e5ae9928dd7710b6d64fa6652e694f46768c3e44c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `68c1ecf8f0ff13e0bc3f2d2e5ae9928dd7710b6d64fa6652e694f46768c3e44c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/io_traits_interface_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/common/io_traits_interface_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/io_traits_interface_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/io_traits_interface_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/io_traits_interface_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/io_traits_interface_contract_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'implements byte and text read/write behavior' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/io_traits_interface_contract_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'implements all seek origins and rejects negative positions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/io_traits_interface_contract_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'closes deterministically and rejects every post-close operation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
