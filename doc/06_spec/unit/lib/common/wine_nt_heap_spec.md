# Wine Nt Heap Specification

> Tests covering Wine NT heap bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Nt Heap Specification

## Scenarios

### Wine NT heap bridge

#### lists the modeled process heap calls

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lists the modeled process heap calls
   - Expected: calls.len() equals `3`
   - Expected: calls[0] equals `GetProcessHeap`
   - Expected: calls[1] equals `HeapAlloc`
   - Expected: calls[2] equals `HeapFree`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists the modeled process heap calls")
val calls = wine_nt_heap_required_calls()
expect(calls.len()).to_equal(3)
expect(calls[0]).to_equal("GetProcessHeap")
expect(calls[1]).to_equal("HeapAlloc")
expect(calls[2]).to_equal("HeapFree")
```

</details>

#### blocks heap use until the process heap exists

- blocks heap use until the process heap exists
   - Expected: heap.ready is false
   - Expected: result.ok is false
   - Expected: result.state equals `missing-process-heap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks heap use until the process heap exists")
val heap = wine_nt_process_heap_new(wine_vm_space_new(), false)
val result = wine_nt_heap_alloc(heap, 0x70000000, 16)
expect(heap.ready).to_equal(false)
expect(result.ok).to_equal(false)
expect(result.state).to_equal("missing-process-heap")
```

</details>

#### returns the deterministic process heap handle

- returns the deterministic process heap handle
   - Expected: result.ok is true
   - Expected: result.ptr equals `0x70000000`
   - Expected: result.state equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the deterministic process heap handle")
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val result = wine_nt_get_process_heap(heap)
expect(result.ok).to_equal(true)
expect(result.ptr).to_equal(0x70000000)
expect(result.state).to_equal("ready")
```

</details>

#### allocates deterministic process heap blocks

- allocates deterministic process heap blocks
   - Expected: first.ok is true
   - Expected: first.ptr equals `0x71000000`
   - Expected: second.ok is true
   - Expected: second.ptr equals `0x71000020`
   - Expected: second.heap.blocks.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates deterministic process heap blocks")
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val first = wine_nt_heap_alloc(heap, heap.handle, 32)
val second = wine_nt_heap_alloc(first.heap, heap.handle, 16)
expect(first.ok).to_equal(true)
expect(first.ptr).to_equal(0x71000000)
expect(second.ok).to_equal(true)
expect(second.ptr).to_equal(0x71000020)
expect(second.heap.blocks.len()).to_equal(2)
```

</details>

#### rejects invalid heap handles and sizes

- rejects invalid heap handles and sizes
   - Expected: wine_nt_heap_alloc(heap, 99, 16).state equals `invalid-heap-handle`
   - Expected: wine_nt_heap_alloc(heap, heap.handle, 0).state equals `invalid-size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid heap handles and sizes")
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
expect(wine_nt_heap_alloc(heap, 99, 16).state).to_equal("invalid-heap-handle")
expect(wine_nt_heap_alloc(heap, heap.handle, 0).state).to_equal("invalid-size")
```

</details>

#### frees allocated blocks and records double frees

- frees allocated blocks and records double frees
   - Expected: freed.ok is true
   - Expected: freed.state equals `freed`
   - Expected: again.ok is false
   - Expected: again.state equals `double-free`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frees allocated blocks and records double frees")
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val allocated = wine_nt_heap_alloc(heap, heap.handle, 64)
val freed = wine_nt_heap_free(allocated.heap, heap.handle, allocated.ptr)
val again = wine_nt_heap_free(freed.heap, heap.handle, allocated.ptr)
expect(freed.ok).to_equal(true)
expect(freed.state).to_equal("freed")
expect(again.ok).to_equal(false)
expect(again.state).to_equal("double-free")
```

</details>

#### rejects frees for unknown pointers

- rejects frees for unknown pointers
   - Expected: result.ok is false
   - Expected: result.state equals `invalid-pointer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects frees for unknown pointers")
val heap = wine_nt_process_heap_new(wine_vm_space_new(), true)
val result = wine_nt_heap_free(heap, heap.handle, 0x72000000)
expect(result.ok).to_equal(false)
expect(result.state).to_equal("invalid-pointer")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_nt_heap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine NT heap bridge.
- Wine NT heap bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e7607ad8fc31193d1dfeaea3d201ed22014f08b9ed392a30f472c578aa7a28aa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e7607ad8fc31193d1dfeaea3d201ed22014f08b9ed392a30f472c578aa7a28aa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e7607ad8fc31193d1dfeaea3d201ed22014f08b9ed392a30f472c578aa7a28aa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/wine_nt_heap_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_nt_heap_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_nt_heap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_nt_heap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_nt_heap_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_nt_heap_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists the modeled process heap calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_nt_heap_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks heap use until the process heap exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_nt_heap_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the deterministic process heap handle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
