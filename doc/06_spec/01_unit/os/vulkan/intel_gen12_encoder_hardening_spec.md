# Intel Gen12 Command-Stream Encoder — Hardening (Lane H2)

> The reader is an engineer asking: *does this encoder reject impossible input,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Intel Gen12 Command-Stream Encoder — Hardening (Lane H2)

The reader is an engineer asking: *does this encoder reject impossible input,

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver |
| Status | In Progress — hardening pass over the checked-in encoder; |
| Source | `test/01_unit/os/vulkan/intel_gen12_encoder_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The reader is an engineer asking: *does this encoder reject impossible input,
or does it silently emit a malformed dword the GPU will consume far away from
where the mistake was made?* This spec exercises exactly the checked
(`Result`-returning) entry points added for hardening, asserting the TYPED
error and offending field for each rejection — not a bare "invalid input".

## Scope and Preconditions

Pure computation, no GPU/board required.

## Primary Workflow

Drive `dword_length_field_checked`, `gfxpipe_header_checked`,
`encode_gfxpipe_state_packet_checked`, and `mi_fixed_header_checked` with
inputs at and past their documented bit-field boundaries, and confirm each
rejection names the field that was actually wrong.

## Key Concepts

| Concept | Description |
|---------|-------------|
| DWord Length underflow | `total_dwords < 2` would make `total_dwords - 2` negative, which packed into an unsigned bit field wraps to a huge value — a runaway GPU read |
| DWord Length overflow | `total_dwords` too large for the 8-bit field |
| Zero/empty decision | an empty-operand GFXPIPE packet has `total_dwords == 1`, which the underflow check rejects — this is the format's own rule (2 header dwords always assumed), not a policy choice |

## Recovery and Troubleshooting

A red here after touching `encoder_intel_gen12.spl` means a checked function
no longer rejects a case it used to, or rejects with the wrong field name —
check the failing field name in the assertion against the bit-width comment
next to the corresponding constant.

## Compatibility and Limitations

Does not touch `soc_profile.spl` or any capability flag. Hardening the
encoder does not make this driver runnable.

## Scenarios

### Gen12 DWord Length underflow (highest-value check)

#### rejects total_dwords below 2, naming total_dwords

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects total_dwords below 2, naming total_dwords
- ask for a packet smaller than the header itself allows


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects total_dwords below 2, naming total_dwords")
step("ask for a packet smaller than the header itself allows")
val result = dword_length_field_checked(1)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "total_dwords")
```

</details>

#### rejects total_dwords of 0, not wrapping to a huge unsigned value

- rejects total_dwords of 0, not wrapping to a huge unsigned value
- ask for a zero-size packet


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects total_dwords of 0, not wrapping to a huge unsigned value")
step("ask for a zero-size packet")
val result = dword_length_field_checked(0)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "total_dwords")
```

</details>

#### accepts the minimum legal total_dwords of 2, encoding length field 0

- accepts the minimum legal total_dwords of 2, encoding length field 0
- ask for the smallest legal packet


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts the minimum legal total_dwords of 2, encoding length field 0")
step("ask for the smallest legal packet")
val length_field = dword_length_field_checked(2).unwrap()
assert_equal(length_field, 0)
```

</details>

### Gen12 DWord Length overflow

#### rejects total_dwords beyond the 8-bit field's range, naming total_dwords

- rejects total_dwords beyond the 8-bit field's range, naming total_dwords
- ask for a packet larger than 257 total dwords


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects total_dwords beyond the 8-bit field's range, naming total_dwords")
step("ask for a packet larger than 257 total dwords")
val result = dword_length_field_checked(258)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "total_dwords")
```

</details>

#### accepts the maximum legal total_dwords of 257

- accepts the maximum legal total_dwords of 257
- ask for the largest legal packet


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts the maximum legal total_dwords of 257")
step("ask for the largest legal packet")
val length_field = dword_length_field_checked(257).unwrap()
assert_equal(length_field, 255)
```

</details>

### Gen12 GFXPIPE header field-width overflow

#### rejects a pipeline_opcode beyond the 13-bit field, naming pipeline_opcode

- rejects a pipeline_opcode beyond the 13-bit field, naming pipeline_opcode
- request an out-of-range pipeline_opcode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a pipeline_opcode beyond the 13-bit field, naming pipeline_opcode")
step("request an out-of-range pipeline_opcode")
val result = gfxpipe_header_checked(8192, 4)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "pipeline_opcode")
```

</details>

#### rejects an empty-operand packet via the underflow path, naming total_dwords

- rejects an empty-operand packet via the underflow path, naming total_dwords
- build a GFXPIPE header for a packet with total_dwords == 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects an empty-operand packet via the underflow path, naming total_dwords")
step("build a GFXPIPE header for a packet with total_dwords == 1")
val result = gfxpipe_header_checked(0, 1)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "total_dwords")
```

</details>

### Gen12 checked GFXPIPE state packet

#### round-trips declared length to the emitted dword count

- round-trips declared length to the emitted dword count
- encode a 2-operand-dword state packet


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("round-trips declared length to the emitted dword count")
step("encode a 2-operand-dword state packet")
val dwords = encode_gfxpipe_state_packet_checked(5, [0x11, 0x22]).unwrap()
val declared_length = decode_gfxpipe_length_field(dwords[0])
val declared_total = total_dwords_from_length_field(declared_length)
assert_equal(declared_total, dwords.len())
assert_equal(dwords.len(), 3)
```

</details>

#### rejects an empty operand list, naming total_dwords

- rejects an empty operand list, naming total_dwords
- encode a state packet with no operands


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects an empty operand list, naming total_dwords")
step("encode a state packet with no operands")
val result = encode_gfxpipe_state_packet_checked(5, [])
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "total_dwords")
```

</details>

### Gen12 MI opcode field-width overflow

#### rejects an MI opcode beyond the 6-bit field, naming opcode

- rejects an MI opcode beyond the 6-bit field, naming opcode
- request an out-of-range MI opcode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects an MI opcode beyond the 6-bit field, naming opcode")
step("request an out-of-range MI opcode")
val result = mi_fixed_header_checked(64)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "opcode")
```

</details>

#### accepts an in-range MI opcode

- accepts an in-range MI opcode
- request MI_NOOP's opcode explicitly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts an in-range MI opcode")
step("request MI_NOOP's opcode explicitly")
val header = mi_fixed_header_checked(0).unwrap()
assert_equal(header, 0)
```

</details>

### Gen12 encoder sabotage

#### goes RED naming total_dwords when the underflow guard is removed

- goes RED naming total_dwords when the underflow guard is removed
- this scenario documents the sabotage performed out-of-band:
- removing the `total_dwords < 2` check from dword_length_field_checked
- makes total_dwords=1 succeed with length_field=-1 instead of erroring
- re-assert the guard is present: total_dwords=1 must still be rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("goes RED naming total_dwords when the underflow guard is removed")
step("this scenario documents the sabotage performed out-of-band:")
step("removing the `total_dwords < 2` check from dword_length_field_checked")
step("makes total_dwords=1 succeed with length_field=-1 instead of erroring")
step("re-assert the guard is present: total_dwords=1 must still be rejected")
val result = dword_length_field_checked(1)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "total_dwords")
```

</details>

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
- `REQ-BOARD-VULKAN-001`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fc20c9ea39703ecb95e28ee6c83afa7dfe21654cc61114344fe43cc2d882d3ad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fc20c9ea39703ecb95e28ee6c83afa7dfe21654cc61114344fe43cc2d882d3ad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fc20c9ea39703ecb95e28ee6c83afa7dfe21654cc61114344fe43cc2d882d3ad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/vulkan/intel_gen12_encoder_hardening_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/intel_gen12_encoder_hardening_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/os/vulkan/intel_gen12_encoder_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/os/vulkan/intel_gen12_encoder_hardening_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/vulkan/intel_gen12_encoder_hardening_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects total_dwords below 2, naming total_dwords' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/intel_gen12_encoder_hardening_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects total_dwords of 0, not wrapping to a huge unsigned value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/intel_gen12_encoder_hardening_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the minimum legal total_dwords of 2, encoding length field 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
