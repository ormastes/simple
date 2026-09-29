# Authenticated Media Parser Specification

> Tests covering authenticated media parser architecture parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Authenticated Media Parser Specification

## Scenarios

### authenticated media parser architecture parity

#### decodes RV64 and x86_64 admission fields identically

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- decodes RV64 and x86_64 admission fields identically
   - Expected: rv_mount.? is true
   - Expected: x86_mount.? is true
   - Expected: rv_mount.unwrap() equals `x86_mount.unwrap()`
   - Expected: rv_generation.unwrap() equals `x86_generation.unwrap()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("decodes RV64 and x86_64 admission fields identically")
val rv_mount = authenticated_media_u64_field_v1(rv64_admission_record(), "mount_id")
val x86_mount = authenticated_media_u64_field_v1(x86_64_admission_record(), "mount_id")
val rv_generation = authenticated_media_u64_field_v1(rv64_admission_record(), "file_generation")
val x86_generation = authenticated_media_u64_field_v1(x86_64_admission_record(), "file_generation")
expect(rv_mount.?).to_equal(true)
expect(x86_mount.?).to_equal(true)
expect(rv_mount.unwrap()).to_equal(x86_mount.unwrap())
expect(rv_generation.unwrap()).to_equal(x86_generation.unwrap())
```

</details>

#### rejects absent duplicate empty and malformed fields for both adapters

- rejects absent duplicate empty and malformed fields for both adapters
   - Expected: authenticated_media_field_v1("key=first\nkey=second\n", "key").? is false
   - Expected: authenticated_media_field_v1("key=\n", "key").? is false
   - Expected: authenticated_media_field_v1("other=value\n", "key").? is false
   - Expected: authenticated_media_field_v1("key=value\n", "key=value").? is false
   - Expected: authenticated_media_u64_field_v1("mount_id=-1\n", "mount_id").? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects absent duplicate empty and malformed fields for both adapters")
expect(authenticated_media_field_v1("key=first\nkey=second\n", "key").?).to_equal(false)
expect(authenticated_media_field_v1("key=\n", "key").?).to_equal(false)
expect(authenticated_media_field_v1("other=value\n", "key").?).to_equal(false)
expect(authenticated_media_field_v1("key=value\n", "key=value").?).to_equal(false)
expect(authenticated_media_u64_field_v1("mount_id=-1\n", "mount_id").?).to_equal(false)
```

</details>

#### parses checked decimal u64 fields and enforces the mount zero policy

- parses checked decimal u64 fields and enforces the mount zero policy
   - Expected: maximum.? is true
   - Expected: maximum.unwrap() equals `18446744073709551615u64`
   - Expected: authenticated_media_u64_field_v1("mount_id=0\n", "mount_id").? is false
   - Expected: zero_generation.? is true
   - Expected: zero_generation.unwrap() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("parses checked decimal u64 fields and enforces the mount zero policy")
val maximum = authenticated_media_u64_field_v1(
    "file_id=18446744073709551615\n", "file_id")
expect(maximum.?).to_equal(true)
expect(maximum.unwrap()).to_equal(18446744073709551615u64)
expect(authenticated_media_u64_field_v1("mount_id=0\n", "mount_id").?).to_equal(false)
val zero_generation = authenticated_media_u64_field_v1(
    "mount_generation=0\n", "mount_generation")
expect(zero_generation.?).to_equal(true)
expect(zero_generation.unwrap()).to_equal(0u64)
```

</details>

#### rejects alpha empty whitespace signed and overflowing u64 fields

- rejects alpha empty whitespace signed and overflowing u64 fields
   - Expected: authenticated_media_u64_field_v1("file_id=12a3\n", "file_id").? is false
   - Expected: authenticated_media_u64_field_v1("file_id=\n", "file_id").? is false
   - Expected: authenticated_media_u64_field_v1("file_id= 1\n", "file_id").? is false
   - Expected: authenticated_media_u64_field_v1("file_id=1 \n", "file_id").? is false
   - Expected: authenticated_media_u64_field_v1("file_id=1\t\n", "file_id").? is false
   - Expected: authenticated_media_u64_field_v1("file_id=+1\n", "file_id").? is false
   - Expected: authenticated_media_u64_field_v1("file_id=-1\n", "file_id").? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects alpha empty whitespace signed and overflowing u64 fields")
expect(authenticated_media_u64_field_v1("file_id=12a3\n", "file_id").?).to_equal(false)
expect(authenticated_media_u64_field_v1("file_id=\n", "file_id").?).to_equal(false)
expect(authenticated_media_u64_field_v1("file_id= 1\n", "file_id").?).to_equal(false)
expect(authenticated_media_u64_field_v1("file_id=1 \n", "file_id").?).to_equal(false)
expect(authenticated_media_u64_field_v1("file_id=1\t\n", "file_id").?).to_equal(false)
expect(authenticated_media_u64_field_v1("file_id=+1\n", "file_id").?).to_equal(false)
expect(authenticated_media_u64_field_v1("file_id=-1\n", "file_id").?).to_equal(false)
expect(authenticated_media_u64_field_v1(
    "file_id=18446744073709551616\n", "file_id").?).to_equal(false)
```

</details>

#### decodes canonical lowercase signature bytes and fails closed otherwise

- decodes canonical lowercase signature bytes and fails closed otherwise
   - Expected: decoded.len() equals `3`
   - Expected: decoded[0] equals `0u8`
   - Expected: decoded[1] equals `165u8`
   - Expected: decoded[2] equals `255u8`
   - Expected: authenticated_media_hex_bytes_v1("abc").len() equals `0`
   - Expected: authenticated_media_hex_bytes_v1("AA").len() equals `0`
   - Expected: authenticated_media_hex_bytes_v1("0g").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("decodes canonical lowercase signature bytes and fails closed otherwise")
val decoded = authenticated_media_hex_bytes_v1("00a5ff")
expect(decoded.len()).to_equal(3)
expect(decoded[0]).to_equal(0u8)
expect(decoded[1]).to_equal(165u8)
expect(decoded[2]).to_equal(255u8)
expect(authenticated_media_hex_bytes_v1("abc").len()).to_equal(0)
expect(authenticated_media_hex_bytes_v1("AA").len()).to_equal(0)
expect(authenticated_media_hex_bytes_v1("0g").len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/authenticated_media_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering authenticated media parser architecture parity.
- authenticated media parser architecture parity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `ad2f9bc4b7c2db7263ecaa20628353535250478eb847978a0116ca953d8b7df2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ad2f9bc4b7c2db7263ecaa20628353535250478eb847978a0116ca953d8b7df2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ad2f9bc4b7c2db7263ecaa20628353535250478eb847978a0116ca953d8b7df2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/kernel/loader/authenticated_media_parser_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/loader/authenticated_media_parser_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/loader/authenticated_media_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/loader/authenticated_media_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/loader/authenticated_media_parser_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/loader/authenticated_media_parser_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes RV64 and x86_64 admission fields identically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/authenticated_media_parser_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects absent duplicate empty and malformed fields for both adapters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/authenticated_media_parser_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses checked decimal u64 fields and enforces the mount zero policy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
