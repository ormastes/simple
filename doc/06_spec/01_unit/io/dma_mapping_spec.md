# Dma Mapping Specification

> Tests covering canonical DMA mapping metadata.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dma Mapping Specification

## Scenarios

### canonical DMA mapping metadata

#### requires exact physical proof before contiguous address arithmetic

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires exact physical proof before contiguous address arithmetic
   - Expected: dma_shared_mapping(buffer, DmaDir.ToDevice, dma_contiguous_layout(wrong), 1).is_err() is true
   - Expected: dma_mapping_can_use_contiguous(mapping) is false
   - Expected: mapping.state equals `DmaMappingState.Unmapped`
   - Expected: mapped.state equals `DmaMappingState.CpuOwned`
   - Expected: dma_mapping_can_use_contiguous(mapped) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-IO
step("requires exact physical proof before contiguous address arithmetic")
val buffer = _shared_dma_buffer()
val wrong = dma_segment(0x1000, 0x9000, 0xA000, 4096)
expect(dma_shared_mapping(buffer, DmaDir.ToDevice, dma_contiguous_layout(wrong), 1).is_err()).to_equal(true)

val exact = dma_segment(0x1000, 0x8000, 0xA000, 4096)
val mapping = dma_shared_mapping(buffer, DmaDir.ToDevice, dma_contiguous_layout(exact), 1).unwrap()
expect(dma_mapping_can_use_contiguous(mapping)).to_equal(false)
val mapped = dma_mapping_map(mapping).unwrap()
expect(mapping.state).to_equal(DmaMappingState.Unmapped)
expect(mapped.state).to_equal(DmaMappingState.CpuOwned)
expect(dma_mapping_can_use_contiguous(mapped)).to_equal(true)
```

</details>

#### preserves explicit scatter segments and ordered ownership

- preserves explicit scatter segments and ordered ownership
   - Expected: initial.segment_count() equals `2`
   - Expected: dma_mapping_can_use_contiguous(initial) is false
   - Expected: dma_mapping_unmap(device).is_err() is true
   - Expected: released.mapping_token equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-IO
step("preserves explicit scatter segments and ordered ownership")
val buffer = _shared_dma_buffer()
val segments = [
    dma_segment(0x1000, 0x8000, 0xA000, 2048),
    dma_segment(0x1800, 0xC000, 0xE000, 2048)
]
val initial = dma_shared_mapping(buffer, DmaDir.Bidirectional, dma_scatter_layout(segments), 2).unwrap()
expect(initial.segment_count()).to_equal(2)
expect(dma_mapping_can_use_contiguous(initial)).to_equal(false)

val mapped = dma_mapping_map(initial).unwrap()
val device = dma_mapping_sync_for_device(mapped).unwrap()
expect(dma_mapping_unmap(device).is_err()).to_equal(true)
val cpu = dma_mapping_sync_for_cpu(device).unwrap()
val unmapped = dma_mapping_unmap(cpu).unwrap()
val released = dma_mapping_release(unmapped).unwrap()
expect(released.mapping_token).to_equal(2)
```

</details>

#### rejects sync transitions that violate direction

- rejects sync transitions that violate direction
   - Expected: dma_mapping_sync_for_cpu(mapped_to_device).is_err() is true
   - Expected: dma_mapping_sync_for_device(mapped_from_device).is_err() is true
   - Expected: dma_mapping_sync_for_cpu(sync_bidir_to_device).is_err() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-IO
step("rejects sync transitions that violate direction")
val buffer = _shared_dma_buffer()
val exact = dma_segment(0x1000, 0x8000, 0xA000, 4096)
val to_device = dma_shared_mapping(buffer, DmaDir.ToDevice, dma_contiguous_layout(exact), 11).unwrap()
val mapped_to_device = dma_mapping_map(to_device).unwrap()
expect(dma_mapping_sync_for_cpu(mapped_to_device).is_err()).to_equal(true)

val from_device = dma_shared_mapping(buffer, DmaDir.FromDevice, dma_contiguous_layout(exact), 12).unwrap()
val mapped_from_device = dma_mapping_map(from_device).unwrap()
expect(dma_mapping_sync_for_device(mapped_from_device).is_err()).to_equal(true)

val bidirectional = dma_shared_mapping(buffer, DmaDir.Bidirectional, dma_contiguous_layout(exact), 13).unwrap()
val mapped_bidir = dma_mapping_map(bidirectional).unwrap()
val sync_bidir_to_device = dma_mapping_sync_for_device(mapped_bidir).unwrap()
expect(dma_mapping_sync_for_cpu(sync_bidir_to_device).is_err()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | Active |
| Source | `test/01_unit/io/dma_mapping_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering canonical DMA mapping metadata.
- canonical DMA mapping metadata

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-IO`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `05867c3fa9f7bb984f121d5e32901249b9d822fffc88effce9b32094f60207ec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `05867c3fa9f7bb984f121d5e32901249b9d822fffc88effce9b32094f60207ec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `05867c3fa9f7bb984f121d5e32901249b9d822fffc88effce9b32094f60207ec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/io/dma_mapping_spec.spl
mirror: doc/06_spec/01_unit/io/dma_mapping_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/io/dma_mapping_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/io/dma_mapping_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/io/dma_mapping_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/io/dma_mapping_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires exact physical proof before contiguous address arithmetic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/io/dma_mapping_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves explicit scatter segments and ordered ownership' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/io/dma_mapping_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects sync transitions that violate direction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
