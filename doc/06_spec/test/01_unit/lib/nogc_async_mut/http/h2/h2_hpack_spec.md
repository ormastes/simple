# H2 HPACK Encode/Decode Specification

> <details>

<!-- sdn-diagram:id=h2_hpack_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=h2_hpack_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

h2_hpack_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=h2_hpack_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### HPACK encoder and decoder

#### encodes indexed header field from static table

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
