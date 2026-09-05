# Command-Stream Boundary Schema — Intel Gen12 / anv (Lane R4 / B3)

> The reader is an engineer asking: *what must a future Intel Gen12 command-

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Command-Stream Boundary Schema — Intel Gen12 / anv (Lane R4 / B3)

The reader is an engineer asking: *what must a future Intel Gen12 command-

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver |
| Status | In Progress — reference schema only, no candidate encoder exists |
| Plan | doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md |
| Source | `test/01_unit/os/vulkan/cmdstream_boundary_intel_gen12_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The reader is an engineer asking: *what must a future Intel Gen12 command-
stream encoder produce, and how would it be judged against Mesa `anv`?*
`backend_intel_gen12.spl` declares `submit_implemented: false` — there is no
candidate encoder anywhere in this tree — and this capture host has no Intel
GPU at all (two NVIDIA devices only, confirmed via `lspci`). So this file
cannot exercise a real candidate. It pins the CANONICAL SCHEMA and the
comparator the eventual encoder must satisfy, against a synthetic (clearly
labelled, not captured) reference packet sequence.

## Scope and Preconditions

No GPU, board, or Mesa build is needed to run this file — it exercises pure
packet-model and canonicalization logic in
`boundary_cmdstream_canonicalize.spl`.

## Primary Workflow

Build the synthetic Gen12 reference stream, confirm it compares structurally
equal to itself (the honest green case: same sequence, only per-run-varying
fields normalized), then sabotage a copy by reordering/dropping a packet and
confirm the comparator names the first diverging index.

## Key Concepts

| Concept | Description |
|---------|-------------|
| CmdPacket | opcode + dword length + ordered payload fields |
| Dropped dimension | address / bo_handle / timestamp / zero-valued mbz — named, not heuristic |
| structural_equal | byte_exact over the canonical sequence; no tolerance |

## Related Specifications

- [Board vulkan counterpart plan](board_vulkan_counterpart_plan_spec.spl) — declares `byte_exact` for this boundary
- [SPIR-V boundary canonicalizer](../../../../src/os/drivers/gpu/board_vulkan/boundary_spirv_canonicalize.spl) — sibling boundary, same discipline (explicit allowlist, not reachability heuristics)

## Evidence and Provenance

`lspci -nn` on this host lists only `10de:2230` (GA102GL "RTX A6000") and
`10de:1e02` (TU102 "TITAN RTX") as VGA controllers; no Intel display
controller is present. `vulkaninfo` against `intel_icd.json` fails with
"Failed to detect any valid GPUs". `intel_error_decode`/`aubinator`/
`intel_dump_gpu` are not installed. This is a hardware-absence gap, not a
missing-tool gap, and is filed rather than worked around with a fabricated
capture presented as real anv output.

## Recovery and Troubleshooting

A red here that names a packet index means the comparator caught a real
structural divergence — check `cmd_stream_first_divergence` against both
canonical streams before assuming the fixture itself is wrong.

## Compatibility and Limitations

The candidate side of this boundary reports `ProviderStatus.unavailable`
until an Intel Gen12 encoder exists (see
`src/os/drivers/gpu/board_vulkan/backend_intel_gen12.spl`); a real
counterpart run is therefore correctly rejected today. This file only proves
the reference schema and comparator are sound, so that encoder has a true
oracle to develop against.

## Scenarios

### command-stream boundary schema

#### builds a five-packet synthetic Gen12 reference stream

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds a five-packet synthetic Gen12 reference stream
- read the fixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("builds a five-packet synthetic Gen12 reference stream")
step("read the fixture")
assert_equal(synthetic_gen12_reference_stream().len(), 5)
```

</details>

#### normalizes address, handle and timestamp values but keeps the fields present

- normalizes address, handle and timestamp values but keeps the fields present
- canonicalize the reference stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("normalizes address, handle and timestamp values but keeps the fields present")
step("canonicalize the reference stream")
val canon = cmd_stream_canonical(synthetic_gen12_reference_stream())
val vb = canon[2]
assert_equal(vb.opcode, "3DSTATE_VERTEX_BUFFERS")
assert_equal(vb.payload[1].name, "bo_handle")
assert_equal(vb.payload[1].value, "<normalized>")
assert_equal(vb.payload[3].name, "address")
assert_equal(vb.payload[3].value, "<normalized>")
```

</details>

#### does not normalize a live operand such as vertex_count

- does not normalize a live operand such as vertex_count
- canonicalize the draw packet


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("does not normalize a live operand such as vertex_count")
step("canonicalize the draw packet")
val canon = cmd_stream_canonical(synthetic_gen12_reference_stream())
val draw = canon[3]
assert_equal(draw.payload[0].name, "vertex_count")
assert_equal(draw.payload[0].value, "3")
```

</details>

#### compares an identical copy as structurally equal despite differing addresses

- compares an identical copy as structurally equal despite differing addresses
- build a copy with different per-run address/handle/timestamp values
- confirm every masked field genuinely differs from the reference before comparing


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("compares an identical copy as structurally equal despite differing addresses")
step("build a copy with different per-run address/handle/timestamp values")
var candidate = clone_stream(synthetic_gen12_reference_stream())
candidate[0] = cmd_packet("MI_BATCH_BUFFER_START", 2, [
    cmd_field("address", "0x111111111"),
    cmd_field("mbz", "0")
])
candidate[2] = cmd_packet("3DSTATE_VERTEX_BUFFERS", 5, [
    cmd_field("buffer_index", "0"),
    cmd_field("bo_handle", "999"),
    cmd_field("buffer_pitch", "12"),
    cmd_field("address", "0x222222222")
])
candidate[3] = cmd_packet("3DPRIMITIVE", 7, [
    cmd_field("vertex_count", "3"),
    cmd_field("start_vertex", "0"),
    cmd_field("instance_count", "1"),
    cmd_field("timestamp", "999999999")
])
step("confirm every masked field genuinely differs from the reference before comparing")
val reference = synthetic_gen12_reference_stream()
assert_true(reference[0].payload[0].value != candidate[0].payload[0].value)
assert_true(reference[2].payload[1].value != candidate[2].payload[1].value)
assert_true(reference[2].payload[3].value != candidate[2].payload[3].value)
assert_true(reference[3].payload[3].value != candidate[3].payload[3].value)
assert_true(cmd_stream_structural_equal(reference, candidate))
assert_equal(cmd_stream_first_divergence(reference, candidate), -1)
```

</details>

### command-stream boundary sabotage

#### goes RED and names the packet index when a live operand is changed

- goes RED and names the packet index when a live operand is changed
- mutate vertex_count (a live, never-masked operand) on the draw packet


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("goes RED and names the packet index when a live operand is changed")
step("mutate vertex_count (a live, never-masked operand) on the draw packet")
var candidate = clone_stream(synthetic_gen12_reference_stream())
candidate[3] = cmd_packet("3DPRIMITIVE", 7, [
    cmd_field("vertex_count", "4"),
    cmd_field("start_vertex", "0"),
    cmd_field("instance_count", "1"),
    cmd_field("timestamp", "1723300000")
])
assert_false(cmd_stream_structural_equal(synthetic_gen12_reference_stream(), candidate))
assert_equal(cmd_stream_first_divergence(synthetic_gen12_reference_stream(), candidate), 3)
```

</details>

#### goes RED and names the packet index when two packets are reordered

- goes RED and names the packet index when two packets are reordered
- swap the topology and vertex-buffers packets


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("goes RED and names the packet index when two packets are reordered")
step("swap the topology and vertex-buffers packets")
var candidate = clone_stream(synthetic_gen12_reference_stream())
val topology = candidate[1]
candidate[1] = candidate[2]
candidate[2] = topology
assert_false(cmd_stream_structural_equal(synthetic_gen12_reference_stream(), candidate))
assert_equal(cmd_stream_first_divergence(synthetic_gen12_reference_stream(), candidate), 1)
```

</details>

#### goes RED and names the truncation point when the final packet is dropped

- goes RED and names the truncation point when the final packet is dropped
- drop MI_BATCH_BUFFER_END from the candidate


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("goes RED and names the truncation point when the final packet is dropped")
step("drop MI_BATCH_BUFFER_END from the candidate")
var candidate = clone_stream(synthetic_gen12_reference_stream())
var truncated: [CmdPacket] = []
var i: i64 = 0
while i < candidate.len() - 1:
    truncated.push(candidate[i])
    i = i + 1
assert_false(cmd_stream_structural_equal(synthetic_gen12_reference_stream(), truncated))
assert_equal(cmd_stream_first_divergence(synthetic_gen12_reference_stream(), truncated), 4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5f61bbb3d3afda7d7b1c21c169af050c8bf0daba39a6818409d923464a9060e1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5f61bbb3d3afda7d7b1c21c169af050c8bf0daba39a6818409d923464a9060e1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5f61bbb3d3afda7d7b1c21c169af050c8bf0daba39a6818409d923464a9060e1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/vulkan/cmdstream_boundary_intel_gen12_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/cmdstream_boundary_intel_gen12_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/os/vulkan/cmdstream_boundary_intel_gen12_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/os/vulkan/cmdstream_boundary_intel_gen12_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/vulkan/cmdstream_boundary_intel_gen12_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a five-packet synthetic Gen12 reference stream' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/cmdstream_boundary_intel_gen12_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes address, handle and timestamp values but keeps the fields present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/cmdstream_boundary_intel_gen12_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not normalize a live operand such as vertex_count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
