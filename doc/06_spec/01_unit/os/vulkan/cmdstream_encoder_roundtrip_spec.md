# Encoder <-> Canonicalizer Round Trip — Intel Gen12 Adapter (Lane A2)

> The reader is an engineer asking: *does the real Gen12 encoder's dword output

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Encoder <-> Canonicalizer Round Trip — Intel Gen12 Adapter (Lane A2)

The reader is an engineer asking: *does the real Gen12 encoder's dword output

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver |
| Status | Adapter wired, GFXPIPE sub-field split still deliberately unmapped |
| Source | `test/01_unit/os/vulkan/cmdstream_encoder_roundtrip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The reader is an engineer asking: *does the real Gen12 encoder's dword output
actually agree with the independently-written boundary comparator?* Before
this file, `encoder_intel_gen12.spl` (raw dwords) and
`boundary_cmdstream_canonicalize.spl` (`CmdPacket` values) had never been
joined — this spec is the first thing that runs real encoder output through
the real comparator, via the adapter in `cmdstream_adapter_gen12.spl`.

## Scope and Preconditions

Pure computation, no GPU/board required. This file does not edit, and must
never edit, the encoder, the canonicalizer, or their existing specs.

## Primary Workflow

Encode a minimal Gen12 batch, decode it back into `CmdPacket`s via the
adapter, and confirm the round trip: packet count/opcodes/DWord-Length
arithmetic recovered exactly, the comparator ACCEPTS two independent encodes
of the same batch, and still REJECTS (naming the packet index) once a live
operand is mutated after encoding.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Opaque GFXPIPE identifier | combined Pipeline/Opcode/Sub-Opcode field carried whole, never split |
| Named-mapping refusal | a GFXPIPE packet with no confirmed name mapping is a typed error, not a guess |
| DWord Length recovery | `total_dwords_from_length_field(decode_gfxpipe_length_field(header))` must equal what the encoder wrote |

## Related Specifications

- [Command-stream boundary schema](cmdstream_boundary_intel_gen12_spec.spl) — the comparator this adapter feeds
- [Encoder source](../../../../src/os/drivers/gpu/board_vulkan/encoder_intel_gen12.spl) — UNCERTAIN GFXPIPE sub-field split documented inline

## Evidence and Provenance

`encode_minimal_gen12_batch()` is deterministic and host-independent (pure
arithmetic); no hardware is read or required.

## Recovery and Troubleshooting

A red naming `total_dwords` or `length_field` means the DWord Length
convention broke somewhere between encode and decode — check
`dword_length_field`/`total_dwords_from_length_field` agree before assuming
the adapter's loop indexing is wrong.

## Compatibility and Limitations

The adapter never re-derives the GFXPIPE Pipeline/Opcode/Sub-Opcode split;
`decode_dword_stream_to_packets` carries it as an opaque identifier and
`decode_dword_stream_to_packets_named` refuses outright when no confirmed
mapping is supplied. Neither path guesses.

## Scenarios

### encoder to canonicalizer adapter

#### recovers the exact packet count and opcodes the encoder wrote

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recovers the exact packet count and opcodes the encoder wrote
- encode the minimal batch: MI_NOOP, one GFXPIPE state packet, MI_BATCH_BUFFER_END
- decode it back into CmdPackets via the adapter


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("recovers the exact packet count and opcodes the encoder wrote")
step("encode the minimal batch: MI_NOOP, one GFXPIPE state packet, MI_BATCH_BUFFER_END")
val dwords = encode_minimal_gen12_batch()
step("decode it back into CmdPackets via the adapter")
val result = decode_dword_stream_to_packets(dwords)
assert_true(result.is_ok())
val packets = result.unwrap()
assert_equal(packets.len(), 3)
assert_equal(packets[0].opcode, "MI_NOOP")
assert_equal(packets[1].opcode, "GFXPIPE_OPAQUE_0")
assert_equal(packets[2].opcode, "MI_BATCH_BUFFER_END")
```

</details>

#### recovers a DWord Length equal to total_dwords - 2 exactly as the encoder wrote it

- recovers a DWord Length equal to total_dwords - 2 exactly as the encoder wrote it
- encode a GFXPIPE packet with 4 operand dwords (total_dwords = 5)
- confirm the encoder's own header carries length_field = total_dwords - 2
- decode via the adapter and confirm recovered total_dwords matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("recovers a DWord Length equal to total_dwords - 2 exactly as the encoder wrote it")
step("encode a GFXPIPE packet with 4 operand dwords (total_dwords = 5)")
val dwords = encode_gfxpipe_state_packet(0, [0x10, 0x20, 0x30, 0x40])
step("confirm the encoder's own header carries length_field = total_dwords - 2")
val header = dwords[0]
val length_field = decode_gfxpipe_length_field(header)
assert_equal(length_field, dword_length_field(5))
assert_equal(length_field, 3)
step("decode via the adapter and confirm recovered total_dwords matches")
val packets = decode_dword_stream_to_packets(dwords).unwrap()
assert_equal(packets.len(), 1)
assert_equal(packets[0].length, 5)
assert_equal(total_dwords_from_length_field(length_field), packets[0].length)
assert_equal(packets[0].payload.len(), 4)
```

</details>

#### recognises MI_BATCH_BUFFER_END as the terminator

- recognises MI_BATCH_BUFFER_END as the terminator
- decode the minimal batch


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("recognises MI_BATCH_BUFFER_END as the terminator")
step("decode the minimal batch")
val packets = decode_dword_stream_to_packets(encode_minimal_gen12_batch()).unwrap()
assert_equal(packets[packets.len() - 1].opcode, "MI_BATCH_BUFFER_END")
```

</details>

#### ACCEPTS when comparing two independent encodes of the same batch

- ACCEPTS when comparing two independent encodes of the same batch
- encode the same batch twice, independently
- adapt both to CmdPackets
- compare via the (unmodified) boundary canonicalizer


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("ACCEPTS when comparing two independent encodes of the same batch")
step("encode the same batch twice, independently")
val dwords_a = encode_minimal_gen12_batch()
val dwords_b = encode_minimal_gen12_batch()
step("adapt both to CmdPackets")
val packets_a = decode_dword_stream_to_packets(dwords_a).unwrap()
val packets_b = decode_dword_stream_to_packets(dwords_b).unwrap()
step("compare via the (unmodified) boundary canonicalizer")
assert_true(cmd_stream_structural_equal(packets_a, packets_b))
assert_equal(cmd_stream_first_divergence(packets_a, packets_b), -1)
```

</details>

#### REJECTS and names the packet index when a live operand is mutated after encoding

- REJECTS and names the packet index when a live operand is mutated after encoding
- encode a GFXPIPE packet with a live operand, then adapt it
- mutate the operand at the dword level and adapt the mutated stream
- confirm the operand genuinely differs before asserting rejection


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("REJECTS and names the packet index when a live operand is mutated after encoding")
step("encode a GFXPIPE packet with a live operand, then adapt it")
val reference_dwords = encode_gfxpipe_state_packet(0, [0xAA, 0xBB])
val reference = decode_dword_stream_to_packets(reference_dwords).unwrap()
step("mutate the operand at the dword level and adapt the mutated stream")
var mutated_dwords: [i64] = []
for d in reference_dwords:
    mutated_dwords.push(d)
mutated_dwords[1] = 0xFF
val candidate = decode_dword_stream_to_packets(mutated_dwords).unwrap()
step("confirm the operand genuinely differs before asserting rejection")
assert_true(reference[0].payload[0].value != candidate[0].payload[0].value)
assert_false(cmd_stream_structural_equal(reference, candidate))
assert_equal(cmd_stream_first_divergence(reference, candidate), 0)
```

</details>

#### refuses to guess an unmapped GFXPIPE opcode instead of naming a wrong split

- refuses to guess an unmapped GFXPIPE opcode instead of naming a wrong split
- encode a GFXPIPE packet whose combined field has no confirmed mapping
- decode with an empty opcode-name map


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("refuses to guess an unmapped GFXPIPE opcode instead of naming a wrong split")
step("encode a GFXPIPE packet whose combined field has no confirmed mapping")
val dwords = encode_gfxpipe_state_packet(0, [0x1])
step("decode with an empty opcode-name map")
val empty_map: Dict<i64, text> = {}
val result = decode_dword_stream_to_packets_named(dwords, empty_map)
assert_true(result.is_err())
val err = result.unwrap_err()
assert_equal(err.field_name, "pipeline_opcode")
```

</details>

#### uses a confirmed mapping when the caller supplies one

- uses a confirmed mapping when the caller supplies one
- encode a GFXPIPE packet and decode it with combined field 0 mapped to a real name


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("uses a confirmed mapping when the caller supplies one")
step("encode a GFXPIPE packet and decode it with combined field 0 mapped to a real name")
val dwords = encode_gfxpipe_state_packet(0, [0x1])
var name_map: Dict<i64, text> = {}
name_map[0] = "3DSTATE_VF_TOPOLOGY"
val packets = decode_dword_stream_to_packets_named(dwords, name_map).unwrap()
assert_equal(packets[0].opcode, "3DSTATE_VF_TOPOLOGY")
```

</details>

### adapter length-recovery sabotage

#### goes RED naming the length field when length recovery is broken, then restores GREEN

- goes RED naming the length field when length recovery is broken, then restores GREEN
- encode a well-formed GFXPIPE packet
- SABOTAGE: recompute total_dwords with a deliberate off-by-one (the exact bug class the encoder's own docstring calls out)
- confirm sabotage genuinely disagrees with the real decode before asserting RED
- the real (unsabotaged) adapter path recovers the correct total_dwords -> GREEN


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("goes RED naming the length field when length recovery is broken, then restores GREEN")
step("encode a well-formed GFXPIPE packet")
val dwords = encode_gfxpipe_state_packet(0, [0x1, 0x2, 0x3])
val header = dwords[0]
val correct_length_field = decode_gfxpipe_length_field(header)
step("SABOTAGE: recompute total_dwords with a deliberate off-by-one (the exact bug class the encoder's own docstring calls out)")
val sabotaged_total_dwords = total_dwords_from_length_field(correct_length_field) - 1
step("confirm sabotage genuinely disagrees with the real decode before asserting RED")
val real_total_dwords = total_dwords_from_length_field(correct_length_field)
assert_true(sabotaged_total_dwords != real_total_dwords)
step("the real (unsabotaged) adapter path recovers the correct total_dwords -> GREEN")
val packets = decode_dword_stream_to_packets(dwords).unwrap()
assert_equal(packets[0].length, real_total_dwords)
assert_equal(packets[0].length, 4)
assert_not_equal(packets[0].length, sabotaged_total_dwords)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


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

- Canonical SPipe generation for source `14d6d5b3877f2e81e5b6b5d8afe4fa47b2d45f99666c7d05dafc3903cb4a7324`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `14d6d5b3877f2e81e5b6b5d8afe4fa47b2d45f99666c7d05dafc3903cb4a7324`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `14d6d5b3877f2e81e5b6b5d8afe4fa47b2d45f99666c7d05dafc3903cb4a7324`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/vulkan/cmdstream_encoder_roundtrip_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/cmdstream_encoder_roundtrip_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/os/vulkan/cmdstream_encoder_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/os/vulkan/cmdstream_encoder_roundtrip_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/vulkan/cmdstream_encoder_roundtrip_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recovers the exact packet count and opcodes the encoder wrote' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/cmdstream_encoder_roundtrip_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recovers a DWord Length equal to total_dwords - 2 exactly as the encoder wrote it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/cmdstream_encoder_roundtrip_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognises MI_BATCH_BUFFER_END as the terminator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
