# TLS Record Protocol Evidence Table

> Uses the production TLS 1.2 record layout owned by `src/os/tls12/tls12_record.spl`: content type, protocol version, big-endian fragment length, then fragment bytes. Exact wire bytes remain the primary oracle; typed rows make the important fields reviewable.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TLS Record Protocol Evidence Table

Uses the production TLS 1.2 record layout owned by `src/os/tls12/tls12_record.spl`: content type, protocol version, big-endian fragment length, then fragment bytes. Exact wire bytes remain the primary oracle; typed rows make the important fields reviewable.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/evidence_showcase.md |
| Plan | doc/03_plan/sys_test/evidence_showcase.md |
| Design | doc/05_design/evidence_showcase.md |
| Research | doc/01_research/local/evidence_showcase.md |
| Source | `test/03_system/app/testing/feature/protocol_evidence_table_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Uses the production TLS 1.2 record layout owned by
`src/os/tls12/tls12_record.spl`: content type, protocol version, big-endian
fragment length, then fragment bytes. Exact wire bytes remain the primary
oracle; typed rows make the important fields reviewable.

**Requirements:** doc/02_requirements/feature/evidence_showcase.md
**Plan:** doc/03_plan/sys_test/evidence_showcase.md
**Design:** doc/05_design/evidence_showcase.md
**Research:** doc/01_research/local/evidence_showcase.md

## Examples

Run this spec and compare the exact encoded TLS record bytes with the typed
content-type, version, length, and payload rows. Invalid masks, overlaps, and
out-of-range fields must fail validation.

## Scenarios

### REQ-EVS-011: typed TLS protocol evidence

#### keeps exact TLS wire bytes primary and publishes typed field rows

- Capture the feature evidence
   - Expected: wire equals `[`
- Verify the structured evidence
- protocol field
- protocol field
- protocol field
   - Expected: result equals `ok`
- Render the evidence for review
   - Expected: fields[0].name equals `content_type`
   - Expected: fields[0].importance equals `critical`
   - Expected: fields[1].importance equals `important`
   - Expected: fields[2].endianness equals `network`
- Publish the showcase link
   - Expected: fields.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture the feature evidence")
val wire = encode_record(TlsRecord12(
    content_type: 0x17u8,
    version_major: 0x03u8,
    version_minor: 0x03u8,
    fragment: [0xCAu8, 0xFEu8]
))
expect(wire).to_equal([
    0x17u8, 0x03u8, 0x03u8, 0x00u8, 0x02u8, 0xCAu8, 0xFEu8
])

step("Verify the structured evidence")
val fields = [
    protocol_field(0, 1, 0, 8, "0xff", "content_type", "0x17", "0x17", "critical"),
    protocol_field(1, 2, 0, 16, "0xffff", "legacy_version", "0x0303", "0x0303", "important"),
    protocol_field(3, 2, 0, 16, "0xffff", "fragment_length", "2", "2", "supporting")
]
val result = scenario_protocol_evidence_validate(fields)
expect(result).to_equal("ok")

step("Render the evidence for review")
expect(fields[0].name).to_equal("content_type")
expect(fields[0].importance).to_equal("critical")
expect(fields[1].importance).to_equal("important")
expect(fields[2].endianness).to_equal("network")

step("Publish the showcase link")
expect(fields.len()).to_equal(3)
val publication = publish_scenario_evidence_status(
    "protocol.crypto.fields",
    ["REQ-EVS-011"],
    "test/03_system/app/testing/feature/protocol_evidence_table_spec.spl",
    "contract",
    "typed wire evidence verified; artifact capture not configured",
    "host-interpreter",
    "tls12-record",
    "bin/simple test test/03_system/app/testing/feature/" +
    "protocol_evidence_table_spec.spl --mode=interpreter"
).unwrap()
expect(publication).to_equal(
    "build/test-artifacts/03_system/app/testing/feature/" +
    "protocol_evidence_table/evidence.sdn"
)
```

</details>

#### rejects overlapping typed field rows

- Capture the feature evidence
- protocol field
- protocol field
- Verify the structured evidence
   - Expected: result equals `overlapping_fields`
- Render the evidence for review
   - Expected: fields[0].byte_length equals `2`
- Publish the showcase link
   - Expected: fields[1].byte_offset equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture the feature evidence")
val fields = [
    protocol_field(1, 2, 0, 16, "0xffff", "legacy_version", "0x0303", "0x0303", "critical"),
    protocol_field(2, 1, 0, 8, "0xff", "version_minor", "0x03", "0x03", "important")
]

step("Verify the structured evidence")
val result = scenario_protocol_evidence_validate(fields)
expect(result).to_equal("overlapping_fields")

step("Render the evidence for review")
expect(fields[0].byte_length).to_equal(2)

step("Publish the showcase link")
expect(fields[1].byte_offset).to_equal(2)
```

</details>

#### rejects a bit field outside its declared byte range

- Capture the feature evidence
- Verify the structured evidence
   - Expected: result equals `invalid_bit_width`
- Render the evidence for review
   - Expected: field.bit_offset equals `7`
- Publish the showcase link
   - Expected: field.bit_width equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture the feature evidence")
val field = protocol_field(
    0, 1, 7, 2, "0x03", "content_type_overflow",
    "0x03", "0x03", "critical"
)

step("Verify the structured evidence")
val result = scenario_protocol_field_evidence_validate(field)
expect(result).to_equal("invalid_bit_width")

step("Render the evidence for review")
expect(field.bit_offset).to_equal(7)

step("Publish the showcase link")
expect(field.bit_width).to_equal(2)
```

</details>

#### rejects mask metadata outside the required hexadecimal form

- Capture the feature evidence
- Verify the structured evidence
   - Expected: result equals `invalid_mask`
- Render the evidence for review
   - Expected: field.mask equals `0b11111111`
- Publish the showcase link
   - Expected: field.importance equals `important`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture the feature evidence")
val field = protocol_field(
    0, 1, 0, 8, "0b11111111", "content_type",
    "0x17", "0x17", "important"
)

step("Verify the structured evidence")
val result = scenario_protocol_field_evidence_validate(field)
expect(result).to_equal("invalid_mask")

step("Render the evidence for review")
expect(field.mask).to_equal("0b11111111")

step("Publish the showcase link")
expect(field.importance).to_equal("important")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/evidence_showcase.md`
- **Plan:** `doc/03_plan/sys_test/evidence_showcase.md`
- **Design:** `doc/05_design/evidence_showcase.md`
- **Research:** `doc/01_research/local/evidence_showcase.md`


</details>
