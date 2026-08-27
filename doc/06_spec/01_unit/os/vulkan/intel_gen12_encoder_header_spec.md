# Intel Gen12 Command-Stream Encoder — Header and Length Encoding (Lane E3)

> The reader is an engineer asking: *does this encoder produce a structurally

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Intel Gen12 Command-Stream Encoder — Header and Length Encoding (Lane E3)

The reader is an engineer asking: *does this encoder produce a structurally

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver |
| Status | In Progress — first real encoder under board_vulkan/, host has no Intel GPU |
| Plan | doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md (stage 3, "submit") |
| Source | `test/01_unit/os/vulkan/intel_gen12_encoder_header_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The reader is an engineer asking: *does this encoder produce a structurally
correct Gen12 command-stream header, and does it get the classic "DWord
Length is total minus 2" off-by-two convention right?* This spec proves both
from the FORMAT's own arithmetic — it never asserts "the encoder returns what
the encoder produced".

## Scope and Preconditions

Pure arithmetic over `encoder_intel_gen12.spl`. No GPU, board, or Mesa build
needed — the host has no Intel GPU at all (see
`doc/08_tracking/bug/cmdstream_boundary_no_intel_gpu_on_capture_host_2026-08-11.md`),
which blocks real submission/readback (stage 4), not this deterministic
encoding step.

## Primary Workflow

Encode MI_NOOP / MI_BATCH_BUFFER_END fixed headers and a GFXPIPE state
packet, decode each back and check the header fields match what was
requested, check the DWord Length field equals actual_dwords - 2 by direct
arithmetic, check a minimal batch terminates correctly, and check an
out-of-range length is rejected.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Command Type | bits [31:29]: 0x0 = MI, 0x3 = GFXPIPE |
| DWord Length | header sub-field = total_dwords_in_packet - 2 (Intel-wide convention) |
| Fixed-length MI command | MI_NOOP / MI_BATCH_BUFFER_END: single dword, no length field at all |

## Related Specifications

- [Command-stream boundary schema](cmdstream_boundary_intel_gen12_spec.spl) — R4's canonical schema/comparator this encoder targets
- [Encoder little-endian emission](intel_gen12_encoder_bytes_spec.spl)

## Evidence and Provenance

Command Type bit position, MI opcode field, and the "length minus 2" DWord
Length convention are documented Intel-wide facts (PRM "Command Structures",
cross-checked against Mesa's `genxml`), not derived from a live capture on
this host (`doc/08_tracking/bug/cmdstream_boundary_no_intel_gpu_on_capture_host_2026-08-11.md`).
The GFXPIPE Pipeline/Opcode/Sub-Opcode internal split is explicitly marked
UNCERTAIN in `encoder_intel_gen12.spl` and is NOT asserted here beyond the
Command Type and Length sub-fields, which are the CONFIDENT parts.

## Recovery and Troubleshooting

A RED here naming `dword_length_field` or a specific bit-extract means the
minus-2 convention (or a header bit-field placement) is broken — check that
function first before assuming the fixture is wrong.

## Compatibility and Limitations

This spec does not assert anything about a SPECIFIC 3DSTATE_* instruction's
internal Pipeline/Opcode/Sub-Opcode split (marked UNCERTAIN in the encoder);
it only proves the Command Type and Length sub-fields, which are generation-
wide and opcode-independent.

## Scenarios

### Intel Gen12 MI fixed-header encoding

#### encodes MI_NOOP with Command Type 0x0 and opcode 0x00

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encodes MI_NOOP with Command Type 0x0 and opcode 0x00
- encode and decode MI_NOOP


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("encodes MI_NOOP with Command Type 0x0 and opcode 0x00")
step("encode and decode MI_NOOP")
val dwords = encode_mi_noop()
assert_equal(dwords.len(), 1)
assert_equal(decode_mi_command_type(dwords[0]), MI_COMMAND_TYPE)
assert_equal(decode_mi_opcode(dwords[0]), MI_OPCODE_NOOP)
```

</details>

#### encodes MI_BATCH_BUFFER_END with Command Type 0x0 and opcode 0x0A

- encodes MI_BATCH_BUFFER_END with Command Type 0x0 and opcode 0x0A
- encode and decode MI_BATCH_BUFFER_END


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("encodes MI_BATCH_BUFFER_END with Command Type 0x0 and opcode 0x0A")
step("encode and decode MI_BATCH_BUFFER_END")
val dwords = encode_mi_batch_buffer_end()
assert_equal(dwords.len(), 1)
assert_equal(decode_mi_command_type(dwords[0]), MI_COMMAND_TYPE)
assert_equal(decode_mi_opcode(dwords[0]), MI_OPCODE_BATCH_BUFFER_END)
```

</details>

#### produces distinct header values for distinct opcodes

- produces distinct header values for distinct opcodes
- compare the two fixed headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("produces distinct header values for distinct opcodes")
step("compare the two fixed headers")
assert_true(mi_fixed_header(MI_OPCODE_NOOP) != mi_fixed_header(MI_OPCODE_BATCH_BUFFER_END))
```

</details>

### Intel Gen12 DWord Length field arithmetic

#### encodes DWord Length as actual_dwords minus 2, not actual_dwords

- encodes DWord Length as actual_dwords minus 2, not actual_dwords
- check the off-by-two convention directly
- check it is NOT the raw dword count (the classic off-by-one/off-by-two bug)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("encodes DWord Length as actual_dwords minus 2, not actual_dwords")
step("check the off-by-two convention directly")
assert_equal(dword_length_field(2), 0)
assert_equal(dword_length_field(3), 1)
assert_equal(dword_length_field(7), 5)
step("check it is NOT the raw dword count (the classic off-by-one/off-by-two bug)")
assert_true(dword_length_field(7) != 7)
assert_true(dword_length_field(7) != 6)
```

</details>

#### round-trips total_dwords through the length field and back

- round-trips total_dwords through the length field and back
- encode then decode for several sizes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("round-trips total_dwords through the length field and back")
step("encode then decode for several sizes")
var n: i64 = 2
while n < 20:
    assert_equal(total_dwords_from_length_field(dword_length_field(n)), n)
    n = n + 1
```

</details>

#### rejects a length field outside the 8-bit range

- rejects a length field outside the 8-bit range
- check boundary and out-of-range values


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a length field outside the 8-bit range")
step("check boundary and out-of-range values")
assert_true(dword_length_field_fits_u8(0))
assert_true(dword_length_field_fits_u8(255))
assert_false(dword_length_field_fits_u8(256))
assert_false(dword_length_field_fits_u8(-1))
```

</details>

#### writes the DWord Length field into a GFXPIPE header and decodes it back exactly

- writes the DWord Length field into a GFXPIPE header and decodes it back exactly
- build a 7-dword GFXPIPE packet header (length field = 5)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("writes the DWord Length field into a GFXPIPE header and decodes it back exactly")
step("build a 7-dword GFXPIPE packet header (length field = 5)")
val header = gfxpipe_header(0, 7)
assert_equal(decode_gfxpipe_command_type(header), GFXPIPE_COMMAND_TYPE)
assert_equal(decode_gfxpipe_length_field(header), dword_length_field(7))
assert_equal(decode_gfxpipe_length_field(header), 5)
```

</details>

### Intel Gen12 GFXPIPE state packet encoding

#### encodes a state packet whose header length field matches its real dword count

- encodes a state packet whose header length field matches its real dword count
- build a 2-operand state packet (3 dwords total)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("encodes a state packet whose header length field matches its real dword count")
step("build a 2-operand state packet (3 dwords total)")
val dwords = encode_gfxpipe_state_packet(0, [0x1111, 0x2222])
assert_equal(dwords.len(), 3)
assert_equal(decode_gfxpipe_length_field(dwords[0]), dword_length_field(3))
assert_equal(dwords[1], 0x1111)
assert_equal(dwords[2], 0x2222)
```

</details>

### Intel Gen12 minimal batch

#### terminates with MI_BATCH_BUFFER_END

- terminates with MI_BATCH_BUFFER_END
- build the minimal batch and check its last dword


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("terminates with MI_BATCH_BUFFER_END")
step("build the minimal batch and check its last dword")
val dwords = encode_minimal_gen12_batch()
assert_true(batch_ends_with_mi_batch_buffer_end(dwords))
```

</details>

#### starts with MI_NOOP and contains at least one GFXPIPE packet before the end

- starts with MI_NOOP and contains at least one GFXPIPE packet before the end
- check the first dword and total length


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("starts with MI_NOOP and contains at least one GFXPIPE packet before the end")
step("check the first dword and total length")
val dwords = encode_minimal_gen12_batch()
assert_equal(decode_mi_command_type(dwords[0]), MI_COMMAND_TYPE)
assert_equal(decode_mi_opcode(dwords[0]), MI_OPCODE_NOOP)
assert_true(dwords.len() >= 4)
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

- **Plan:** `doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md (stage 3, "submit")`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BOARD-VULKAN-001`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e44e60e69477af467b4dda5954f6b8e21d66b9f49656eeb92071e67ca5ece0ad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e44e60e69477af467b4dda5954f6b8e21d66b9f49656eeb92071e67ca5ece0ad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e44e60e69477af467b4dda5954f6b8e21d66b9f49656eeb92071e67ca5ece0ad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/vulkan/intel_gen12_encoder_header_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/intel_gen12_encoder_header_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/os/vulkan/intel_gen12_encoder_header_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/os/vulkan/intel_gen12_encoder_header_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/vulkan/intel_gen12_encoder_header_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes MI_NOOP with Command Type 0x0 and opcode 0x00' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/intel_gen12_encoder_header_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes MI_BATCH_BUFFER_END with Command Type 0x0 and opcode 0x0A' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/intel_gen12_encoder_header_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces distinct header values for distinct opcodes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
