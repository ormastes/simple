# Memory Leveling Dma Runtime Specification

> Tests covering SimpleOS DMA memory-leveling runtime.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Memory Leveling Dma Runtime Specification

## Scenarios

### SimpleOS DMA memory-leveling runtime

#### tracks an allocation through ordered device ownership

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tracks an allocation through ordered device ownership
   - Expected: memory_leveling_runtime_register_dma(42, 7, 0x70000000, 0x200000, 4096, true).ok is true
   - Expected: memory_leveling_runtime_dma_sync_for_device(42, 7).ok is true
   - Expected: manager.get(42).unwrap().state.name equals `device_owned`
   - Expected: manager.get(42).unwrap().in_flight_count equals `1`
   - Expected: memory_leveling_runtime_dma_sync_for_cpu(42, 7).ok is true
   - Expected: manager.get(42).unwrap().state.name equals `cpu_owned`
   - Expected: manager.get(42).unwrap().mapping_count equals `0`
   - Expected: memory_leveling_runtime_unregister_dma(42, 7).ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tracks an allocation through ordered device ownership")
memory_leveling_runtime_reset_for_test()
expect(memory_leveling_runtime_register_dma(42, 7, 0x70000000, 0x200000, 4096, true).ok).to_equal(true)
expect(memory_leveling_runtime_dma_sync_for_device(42, 7).ok).to_equal(true)
var manager = memory_leveling_runtime_manager()
expect(manager.get(42).unwrap().state.name).to_equal("device_owned")
expect(manager.get(42).unwrap().in_flight_count).to_equal(1)
memory_leveling_runtime_replace_manager(manager)

expect(memory_leveling_runtime_dma_sync_for_cpu(42, 7).ok).to_equal(true)
manager = memory_leveling_runtime_manager()
expect(manager.get(42).unwrap().state.name).to_equal("cpu_owned")
expect(manager.get(42).unwrap().mapping_count).to_equal(0)
memory_leveling_runtime_replace_manager(manager)
expect(memory_leveling_runtime_unregister_dma(42, 7).ok).to_equal(true)
```

</details>

#### rejects non-coherent DMA without a cache-maintenance owner

- rejects non-coherent DMA without a cache-maintenance owner
   - Expected: memory_leveling_runtime_register_dma(43, 7, 0x70001000, 0x201000, 4096, false).reason equals `coherency-unproven`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects non-coherent DMA without a cache-maintenance owner")
memory_leveling_runtime_reset_for_test()
expect(memory_leveling_runtime_register_dma(43, 7, 0x70001000, 0x201000, 4096, false).reason).to_equal("coherency-unproven")
```

</details>

#### allocates CPU and DMA identifiers from one manager sequence

- allocates CPU and DMA identifiers from one manager sequence
   - Expected: cpu.ok is true
   - Expected: dma.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("allocates CPU and DMA identifiers from one manager sequence")
memory_leveling_runtime_reset_for_test()
val cpu = memory_leveling_runtime_register_cpu_range(0x60000000, 4096, 7)
val dma = memory_leveling_runtime_register_dma(0, 7, 0x70002000, 0x202000, 4096, true)

expect(cpu.ok).to_equal(true)
expect(dma.ok).to_equal(true)
expect(dma.allocation_ids[0]).to_not_equal(cpu.allocation_ids[0])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/memory_leveling_dma_runtime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS DMA memory-leveling runtime.
- SimpleOS DMA memory-leveling runtime

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ad4fb0b29522f577009342f4a5936879ce217097e201da4f48c57f9df8a4b1a3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ad4fb0b29522f577009342f4a5936879ce217097e201da4f48c57f9df8a4b1a3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ad4fb0b29522f577009342f4a5936879ce217097e201da4f48c57f9df8a4b1a3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/02_integration/os/memory_leveling_dma_runtime_spec.spl
mirror: doc/06_spec/02_integration/os/memory_leveling_dma_runtime_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/os/memory_leveling_dma_runtime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/os/memory_leveling_dma_runtime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/os/memory_leveling_dma_runtime_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/os/memory_leveling_dma_runtime_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks an allocation through ordered device ownership' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/memory_leveling_dma_runtime_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-coherent DMA without a cache-maintenance owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/memory_leveling_dma_runtime_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates CPU and DMA identifiers from one manager sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
