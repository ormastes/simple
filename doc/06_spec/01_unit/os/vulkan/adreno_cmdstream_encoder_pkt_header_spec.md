# Adreno A6xx Command-Stream Encoder — PKT4/PKT7 Header Format (Lane E1)

> The reader is an engineer asking: *does the Adreno PKT4/PKT7 header encoder

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adreno A6xx Command-Stream Encoder — PKT4/PKT7 Header Format (Lane E1)

The reader is an engineer asking: *does the Adreno PKT4/PKT7 header encoder

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver |
| Status | In Progress — encoder exists; SPIR-V stage not yet proven for |
| Plan | doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md |
| Source | `test/01_unit/os/vulkan/adreno_cmdstream_encoder_pkt_header_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The reader is an engineer asking: *does the Adreno PKT4/PKT7 header encoder
in `encoder_adreno.spl` actually implement the documented CP packet format,
or does it just return whatever bytes it happens to produce?* This spec
derives its oracles from the PACKET FORMAT itself — round-tripping a header
through decode, checking the declared dword-count invariant, and checking
range rejection — never from comparing the encoder's output to a captured
value.

## Scope and Preconditions

Pure computation, no GPU/board/Mesa required — this only exercises the
bit-layout functions in `encoder_adreno.spl`.

## Primary Workflow

Build headers with `pkt4_header_checked`/`pkt7_header_checked`, decode them
back with the paired decode functions, and confirm the decoded fields equal
what was asked for. Then build the minimal submission and confirm its total
dword count matches the sum of each packet's declared header + payload
length. Finally confirm out-of-range opcode/regaddr/count is rejected with a
named field, not silently clamped or accepted.

## Key Concepts

| Concept | Description |
|---------|-------------|
| PKT4 | register-range write: 4-bit type tag, 18-bit regaddr, 7-bit count |
| PKT7 | CP command: 4-bit type tag, fixed flag bit, 7-bit opcode, 14-bit count |
| Round-trip oracle | decode(encode(x)) == x, derived from the format, not the impl |

## Related Specifications

- [Intel Gen12 command-stream boundary](cmdstream_boundary_intel_gen12_spec.spl) — sibling lane's packet-model schema (named-opcode packets, not raw bit layout — Adreno's PKT4/PKT7 forms are encoded at the bit level here instead since that is the actual CP wire format)

## Evidence and Provenance

Bit-layout facts and their confidence level are documented inline in
`encoder_adreno.spl`'s header comment. Several fields (reserved-bit widths,
the PKT7 bit-23 flag's exact semantic name, and the exact register-offset
field width) are marked UNCERTAIN there and are not asserted as verified
hardware truth by this spec — only the CONFIDENT fields (type-tag nibble,
opcode width, count widths) are exercised as hard oracles below.

## Recovery and Troubleshooting

A red here after touching `encoder_adreno.spl` means a header/decode pair
disagrees with itself or with the declared bit width — check the failing
field name in the assertion, then re-check the corresponding bit constant.

## Compatibility and Limitations

`soc_profile.board_profile_false_claim` rejects any profile claiming
`submit_implemented` without `spirv_implemented`. This encoder proves the
command-stream ENCODING is real, but the SPIR-V stage for this backend has
not been built or compared against turnip, so `backend_adreno.spl` correctly
keeps all four capability flags false — this spec does not attempt to flip
them, and doing so would itself be the false claim the gate exists to catch.

## Scenarios

### Adreno PKT4 register-write header

#### round-trips type, register address and count through decode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
# @req REQ-BOARD-VULKAN-001
```

</details>

#### rejects a register address beyond the 18-bit field, naming the field

- request an out-of-range regaddr


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("request an out-of-range regaddr")
val result = pkt4_header_checked(PKT4_REGADDR_MASK + 1, 1)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "regaddr")
```

</details>

#### rejects a count beyond the 7-bit field, naming the field

- request an out-of-range count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("request an out-of-range count")
val result = pkt4_header_checked(0x10, PKT4_COUNT_MASK + 1)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "count")
```

</details>

#### emits header-then-payload dwords, one dword per register value

- encode a 3-register write


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("encode a 3-register write")
val dwords = encode_pkt4(0x40, [10, 20, 30]).unwrap()
assert_equal(dwords.len(), 4)
assert_equal(dwords[1], 10)
assert_equal(dwords[2], 20)
assert_equal(dwords[3], 30)
assert_equal(pkt4_decode_count(dwords[0]), 3)
```

</details>

### Adreno PKT7 CP-command header

#### round-trips type, opcode and count through decode

- build a PKT7 header for CP_DRAW_INDX_OFFSET, 2 operand dwords


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build a PKT7 header for CP_DRAW_INDX_OFFSET, 2 operand dwords")
val header = pkt7_header_checked(CP_DRAW_INDX_OFFSET, 2).unwrap()
assert_equal(pkt7_decode_type(header), 7)
assert_equal(pkt7_decode_opcode(header), CP_DRAW_INDX_OFFSET)
assert_equal(pkt7_decode_count(header), 2)
```

</details>

#### rejects an opcode beyond the 7-bit field, naming the field

- request an out-of-range opcode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("request an out-of-range opcode")
val result = pkt7_header_checked(PKT7_OPCODE_MASK + 1, 0)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "opcode")
```

</details>

#### rejects a count beyond the 14-bit field, naming the field

- request an out-of-range count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("request an out-of-range count")
val result = pkt7_header_checked(CP_NOP, PKT7_COUNT_MASK + 1)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "count")
```

</details>

#### emits a header-only packet for a zero-operand command

- encode CP_NOP with no payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("encode CP_NOP with no payload")
val dwords = encode_pkt7(CP_NOP, []).unwrap()
assert_equal(dwords.len(), 1)
assert_equal(pkt7_decode_opcode(dwords[0]), CP_NOP)
assert_equal(pkt7_decode_count(dwords[0]), 0)
```

</details>

### Adreno minimal submission

#### produces a stream whose declared per-packet counts sum to the true dword total

- build the minimal register-write + draw + NOP submission
- re-walk the stream decoding each header's own declared count
- walking header-declared lengths must land exactly on the stream end


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build the minimal register-write + draw + NOP submission")
val stream = adreno_minimal_submission().unwrap()
step("re-walk the stream decoding each header's own declared count")
var i: i64 = 0
var packets: i64 = 0
while i < stream.len():
    val header = stream[i]
    val type_tag = (header >> 28) & 0xF
    var count: i64 = 0
    if type_tag == 4:
        count = pkt4_decode_count(header)
    else:
        count = pkt7_decode_count(header)
    i = i + 1 + count
    packets = packets + 1
step("walking header-declared lengths must land exactly on the stream end")
assert_equal(i, stream.len())
assert_equal(packets, 3)
```

</details>

### Adreno encoder sabotage

#### goes RED naming the count field when the PKT7 count is corrupted

- build a correct header, then flip only the low count bits
- the decoded count no longer matches what was asked for


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build a correct header, then flip only the low count bits")
val header = pkt7_header_checked(CP_DRAW_INDX_OFFSET, 2).unwrap()
val sabotaged = header ^ 0x1
step("the decoded count no longer matches what was asked for")
assert_true(pkt7_decode_count(sabotaged) != 2)
assert_equal(pkt7_decode_count(sabotaged), 3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BOARD-VULKAN-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9c12d0d2da324b93ea9294bfb7cef2214a780287edef330e67f51e17488ca661`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c12d0d2da324b93ea9294bfb7cef2214a780287edef330e67f51e17488ca661`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c12d0d2da324b93ea9294bfb7cef2214a780287edef330e67f51e17488ca661`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/os/vulkan/adreno_cmdstream_encoder_pkt_header_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/adreno_cmdstream_encoder_pkt_header_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=75
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/vulkan/adreno_cmdstream_encoder_pkt_header_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/os/vulkan/adreno_cmdstream_encoder_pkt_header_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/vulkan/adreno_cmdstream_encoder_pkt_header_spec.spl:103:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'round-trips type, register address and count through decode' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/vulkan/adreno_cmdstream_encoder_pkt_header_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a register address beyond the 18-bit field, naming the field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/adreno_cmdstream_encoder_pkt_header_spec.spl:120:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a count beyond the 7-bit field, naming the field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/adreno_cmdstream_encoder_pkt_header_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits header-then-payload dwords, one dword per register value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
