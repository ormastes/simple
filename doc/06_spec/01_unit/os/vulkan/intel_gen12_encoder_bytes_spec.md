# Intel Gen12 Command-Stream Encoder — Little-Endian Byte Emission (Lane E3)

> The reader is an engineer asking: *are the encoder's dwords packed into

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Intel Gen12 Command-Stream Encoder — Little-Endian Byte Emission (Lane E3)

The reader is an engineer asking: *are the encoder's dwords packed into

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver |
| Status | In Progress |
| Source | `test/01_unit/os/vulkan/intel_gen12_encoder_bytes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The reader is an engineer asking: *are the encoder's dwords packed into
bytes in the correct order for an x86-64 host (little-endian), and does a
full minimal batch survive the round trip through byte packing?*

## Scope and Preconditions

Pure arithmetic over `encoder_intel_gen12.spl`. No hardware needed.

## Primary Workflow

Pack a known dword into bytes and check byte order directly against shifts
of the same value (not against the encoder's own prior output), then pack
the minimal batch and check its byte length is exactly 4x the dword count.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Little-endian | least-significant byte first — standard for x86-64 host memory |

## Related Specifications

- [Header and length encoding](intel_gen12_encoder_header_spec.spl)

## Evidence and Provenance

x86-64 is little-endian; Gen12/Xe-LP command streams are written into host-
addressable ring buffers by the i915 DRM driver on this same host CPU, so no
byte-swap is applicable. This is a platform-wide fact, not derived from a
capture.

## Recovery and Troubleshooting

A RED naming `dword_to_le_bytes` means a byte-order regression.

## Compatibility and Limitations

None beyond what is stated above.

## Scenarios

### Intel Gen12 little-endian dword emission

#### emits the least-significant byte first

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits the least-significant byte first
- pack 0x11223344 and check byte order against direct shifts


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("emits the least-significant byte first")
step("pack 0x11223344 and check byte order against direct shifts")
val bytes = dword_to_le_bytes(0x11223344)
assert_equal(bytes.len(), 4)
assert_equal(bytes[0], 0x44)
assert_equal(bytes[1], 0x33)
assert_equal(bytes[2], 0x22)
assert_equal(bytes[3], 0x11)
```

</details>

#### packs zero and all-ones dwords correctly

- packs zero and all-ones dwords correctly
- check both boundary values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("packs zero and all-ones dwords correctly")
step("check both boundary values")
assert_equal(dword_to_le_bytes(0x00000000), [0, 0, 0, 0])
assert_equal(dword_to_le_bytes(0xFFFFFFFF), [0xFF, 0xFF, 0xFF, 0xFF])
```

</details>

#### packs a multi-dword sequence to exactly 4 bytes per dword, in order

- packs a multi-dword sequence to exactly 4 bytes per dword, in order
- pack two dwords and check concatenation order


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("packs a multi-dword sequence to exactly 4 bytes per dword, in order")
step("pack two dwords and check concatenation order")
val bytes = dwords_to_le_bytes([0xAABBCCDD, 0x11223344])
assert_equal(bytes.len(), 8)
assert_equal(bytes[0], 0xDD)
assert_equal(bytes[3], 0xAA)
assert_equal(bytes[4], 0x44)
assert_equal(bytes[7], 0x11)
```

</details>

#### packs the minimal batch to exactly 4x its dword count

- packs the minimal batch to exactly 4x its dword count
- pack the full minimal Gen12 batch


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("packs the minimal batch to exactly 4x its dword count")
step("pack the full minimal Gen12 batch")
val dwords = encode_minimal_gen12_batch()
val bytes = dwords_to_le_bytes(dwords)
assert_equal(bytes.len(), dwords.len() * 4)
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

- Canonical SPipe generation for source `79bb8e3ac965ddcc00317d56e33ada04679f3de8ae9838d2f0d1187b090ede03`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `79bb8e3ac965ddcc00317d56e33ada04679f3de8ae9838d2f0d1187b090ede03`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `79bb8e3ac965ddcc00317d56e33ada04679f3de8ae9838d2f0d1187b090ede03`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/vulkan/intel_gen12_encoder_bytes_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/intel_gen12_encoder_bytes_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/os/vulkan/intel_gen12_encoder_bytes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/os/vulkan/intel_gen12_encoder_bytes_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/vulkan/intel_gen12_encoder_bytes_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits the least-significant byte first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/intel_gen12_encoder_bytes_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'packs zero and all-ones dwords correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/intel_gen12_encoder_bytes_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'packs a multi-dword sequence to exactly 4 bytes per dword, in order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
