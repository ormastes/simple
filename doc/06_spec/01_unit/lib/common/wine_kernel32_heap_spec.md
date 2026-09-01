# Wine Kernel32 Heap Specification

> Tests covering Wine KERNEL32 heap bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Heap Specification

## Scenarios

### Wine KERNEL32 heap bridge

#### executes a bounded HeapAlloc and HeapFree sequence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes a bounded HeapAlloc and HeapFree sequence
   - Expected: result.ok is true
   - Expected: result.ptr equals `0x71000000`
   - Expected: result.size equals `48`
   - Expected: result.operations equals `GetProcessHeap HeapAlloc HeapFree`
   - Expected: result.heap.blocks[0].freed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("executes a bounded HeapAlloc and HeapFree sequence")
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val result = wine_kernel32_execute_heap(["GetProcessHeap", "HeapAlloc", "HeapFree"], heap, 48)

expect(result.ok).to_equal(true)
expect(result.ptr).to_equal(0x71000000)
expect(result.size).to_equal(48)
expect(result.operations).to_equal("GetProcessHeap HeapAlloc HeapFree")
expect(result.heap.blocks[0].freed).to_equal(true)
```

</details>

#### keeps heap dispatch ordered and bounded

- keeps heap dispatch ordered and bounded
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-heap-sequence-expected:GetProcessHeap`
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:VirtualFree`
   - Expected: invalid.ok is false
   - Expected: invalid.error equals `GetProcessHeap:missing-process-heap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps heap dispatch ordered and bounded")
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val out_of_order = wine_kernel32_execute_heap(["HeapAlloc", "GetProcessHeap", "HeapFree"], heap, 16)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-heap-sequence-expected:GetProcessHeap")

val wrong_family = wine_kernel32_execute_heap(["GetProcessHeap", "HeapAlloc", "VirtualFree"], heap, 16)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:VirtualFree")

val invalid = wine_kernel32_execute_heap(["GetProcessHeap", "HeapAlloc", "HeapFree"], wine_nt_process_heap_new(wine_vm_space_new(), false), 16)
expect(invalid.ok).to_equal(false)
expect(invalid.error).to_equal("GetProcessHeap:missing-process-heap")
```

</details>

#### preserves heap state when freeing through KERNEL32

- preserves heap state when freeing through KERNEL32
   - Expected: result.ok is true
   - Expected: result.heap.blocks.len() equals `2`
   - Expected: result.heap.blocks[0].freed is false
   - Expected: result.heap.blocks[1].freed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves heap state when freeing through KERNEL32")
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val seeded = wine_nt_heap_alloc(heap, heap.handle, 12)
val result = wine_kernel32_execute_heap(["GetProcessHeap", "HeapAlloc", "HeapFree"], seeded.heap, 8)

expect(result.ok).to_equal(true)
expect(result.heap.blocks.len()).to_equal(2)
expect(result.heap.blocks[0].freed).to_equal(false)
expect(result.heap.blocks[1].freed).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_heap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine KERNEL32 heap bridge.
- Wine KERNEL32 heap bridge

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4dad3955e33676a721b00acfdf0ed6f8242bffebb4e392bda2519ac8dd7b5803`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4dad3955e33676a721b00acfdf0ed6f8242bffebb4e392bda2519ac8dd7b5803`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4dad3955e33676a721b00acfdf0ed6f8242bffebb4e392bda2519ac8dd7b5803`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/wine_kernel32_heap_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_kernel32_heap_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_kernel32_heap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_kernel32_heap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_kernel32_heap_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_kernel32_heap_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes a bounded HeapAlloc and HeapFree sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_kernel32_heap_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps heap dispatch ordered and bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_kernel32_heap_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves heap state when freeing through KERNEL32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
