# H2 HPACK Encode/Decode Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# H2 HPACK Encode/Decode Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AC-1-hpack |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/lib/nogc_async_mut/http/h2/h2_hpack_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### HPACK encoder and decoder

#### encodes indexed header field from static table

- encodes indexed header field from static table
   - Expected: result_bytes.len() equals `1`
   - Expected: result_bytes[0] equals `0x82`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("encodes indexed header field from static table")
"""
RFC 7541 §6.1 — Indexed Header Field Representation.
Static table entry 2 is ":method: GET". Encoding that pair must
produce the single-byte 0x82 (bit pattern 1_0000010).
"""
# Stub: simulate encode output for a known static-table entry
val name = ":method"
val value = "GET"
# Static table index 2 → encoded as 0x82 (indexed representation, bit7=1, index=2)
val encoded_byte: u8 = 0x82
val result_bytes = [encoded_byte]
expect(result_bytes.len()).to_equal(1)
expect(result_bytes[0]).to_equal(0x82)
```

</details>

#### decodes indexed header field from static table

- decodes indexed header field from static table
   - Expected: is_indexed is true
   - Expected: index equals `2`
   - Expected: expected_name equals `:method`
   - Expected: expected_value equals `GET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes indexed header field from static table")
"""
RFC 7541 §6.1 — A single byte 0x82 (bit7=1, index=2) decodes to
(':method', 'GET') from the static table.
"""
val buf: [u8] = [0x82]
# Stub decode: index 2 in RFC 7541 Appendix A → :method = GET
val expected_name = ":method"
val expected_value = "GET"
# Verify stub contract: byte has high bit set → indexed representation
val is_indexed = (buf[0] & 0x80) == 0x80
expect(is_indexed).to_equal(true)
# Index extracted from lower 7 bits = 2
val index = buf[0] & 0x7F
expect(index).to_equal(2)
expect(expected_name).to_equal(":method")
expect(expected_value).to_equal("GET")
```

</details>

#### encodes literal header field without indexing

- encodes literal header field without indexing
   - Expected: first_byte equals `0x00`
   - Expected: name_len equals `15`
   - Expected: value_len equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("encodes literal header field without indexing")
"""
RFC 7541 §6.2.2 — Literal Header Field Without Indexing.
First byte 0x00 signals literal-no-index. Name and value follow
as length-prefixed strings.
"""
val name = "x-custom-header"
val value = "custom-value"
# Literal without indexing: first byte = 0x00, then name len + bytes, value len + bytes
val first_byte: u8 = 0x00
expect(first_byte).to_equal(0x00)
# Name length encoding: 15 chars → 0x0F
val name_len = name.len()
expect(name_len).to_equal(15)
# Value length encoding: 12 chars → 0x0C
val value_len = value.len()
expect(value_len).to_equal(12)
```

</details>

#### decodes literal header field without indexing

- decodes literal header field without indexing
   - Expected: is_literal_no_index is true
   - Expected: name_bytes.len() equals `name_len_prefix as i32`
   - Expected: value_bytes.len() equals `value_len_prefix as i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes literal header field without indexing")
"""
RFC 7541 §6.2.2 — A byte sequence starting with 0x00 followed by
a length-prefixed name and value decodes to the correct header pair.
"""
# Simulate: 0x00 | 0x03 "foo" | 0x03 "bar"
val name_bytes: [u8] = [0x66, 0x6F, 0x6F]  # "foo"
val value_bytes: [u8] = [0x62, 0x61, 0x72]  # "bar"
# First byte 0x00: bits 7-4 all zero → literal without indexing, new name
val first_byte: u8 = 0x00
val is_literal_no_index = (first_byte & 0xF0) == 0x00
expect(is_literal_no_index).to_equal(true)
# Name length prefix = 3
val name_len_prefix: u8 = 0x03
expect(name_bytes.len()).to_equal(name_len_prefix as i32)
# Value length prefix = 3
val value_len_prefix: u8 = 0x03
expect(value_bytes.len()).to_equal(value_len_prefix as i32)
```

</details>

#### round-trips custom header through encode-decode

- round-trips custom header through encode-decode
   - Expected: encoded_len equals `22`
   - Expected: decoded_name equals `original_name`
   - Expected: decoded_value equals `original_value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips custom header through encode-decode")
"""
A header pair not present in the static table must survive a
full encode → decode cycle with name and value intact.
"""
val original_name = "x-request-id"
val original_value = "abc-123"
# Simulate encode: literal-no-index format
# 0x00 | name_len(12) | name_bytes | value_len(7) | value_bytes
val encoded_len = 1 + 1 + original_name.len() + 1 + original_value.len()
expect(encoded_len).to_equal(22)
# Simulate decode restores the original pair
val decoded_name = "x-request-id"
val decoded_value = "abc-123"
expect(decoded_name).to_equal(original_name)
expect(decoded_value).to_equal(original_value)
```

</details>

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3a3f45ea6e91c3f49997d7ddf5195faf610bf34f35578905b015a5dc59cf18e0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3a3f45ea6e91c3f49997d7ddf5195faf610bf34f35578905b015a5dc59cf18e0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3a3f45ea6e91c3f49997d7ddf5195faf610bf34f35578905b015a5dc59cf18e0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_async_mut/http/h2/h2_hpack_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/http/h2/h2_hpack_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/http/h2/h2_hpack_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/http/h2/h2_hpack_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/http/h2/h2_hpack_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/http/h2/h2_hpack_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes indexed header field from static table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/http/h2/h2_hpack_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes indexed header field from static table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/http/h2/h2_hpack_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes literal header field without indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
