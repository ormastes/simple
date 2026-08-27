# mimalloc_tls_spec

> Verifies that each call returns a fresh MiHeap value with its own

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mimalloc_tls_spec

Verifies that each call returns a fresh MiHeap value with its own

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/alloc/mimalloc_tls_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## mi_heap_new_thread — per-thread independent heap factory

    Verifies that each call returns a fresh MiHeap value with its own
    pages_by_class slots, independent from any global state.

## Scenarios

### mi_heap_new_thread

#### returns a heap with non-empty pages_by_class slots

- returns a heap with non-empty pages_by_class slots


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns a heap with non-empty pages_by_class slots")
val heap = mi_heap_new_thread()
# A fresh independent heap should have pre-allocated class slots
expect(heap.pages_by_class.len()).to_be_greater_than(0)
```

</details>

#### returned heap size_classes is empty (slots built internally)

- returned heap size_classes is empty (slots built internally)
   - Expected: heap.size_classes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returned heap size_classes is empty (slots built internally)")
val heap = mi_heap_new_thread()
expect(heap.size_classes.len()).to_equal(0)
```

</details>

#### two calls return independent heap values

- two calls return independent heap values
   - Expected: heap_a.pages_by_class.len() equals `heap_b.pages_by_class.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("two calls return independent heap values")
val heap_a = mi_heap_new_thread()
val heap_b = mi_heap_new_thread()
# Both should have the same slot count (same table)
expect(heap_a.pages_by_class.len()).to_equal(heap_b.pages_by_class.len())
```

</details>

### mimalloc_thread_init

#### returns a MiThreadHeap with a non-empty heap

- returns a MiThreadHeap with a non-empty heap


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns a MiThreadHeap with a non-empty heap")
val record = mimalloc_thread_init()
expect(record.heap.pages_by_class.len()).to_be_greater_than(0)
```

</details>

#### thread_id is a valid slot index (heap list is non-empty after init)

- thread_id is a valid slot index (heap list is non-empty after init)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("thread_id is a valid slot index (heap list is non-empty after init)")
val record = mimalloc_thread_init()
# usize is always >= 0; verify the heap was actually registered
expect(record.heap.pages_by_class.len()).to_be_greater_than(0)
```

</details>

#### successive inits return different thread_ids

- successive inits return different thread_ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("successive inits return different thread_ids")
val r1 = mimalloc_thread_init()
val r2 = mimalloc_thread_init()
expect(r1.thread_id).to_not_equal(r2.thread_id)
```

</details>

### mimalloc_thread_heap

#### returns a heap after thread_init

- returns a heap after thread_init


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns a heap after thread_init")
val _record = mimalloc_thread_init()
val heap = mimalloc_thread_heap()
# Should return a heap with at least as many slots as the TLS table
expect(heap.pages_by_class.len()).to_be_greater_than(0)
```

</details>

#### heap returned is not a zero-slot placeholder

- heap returned is not a zero-slot placeholder


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("heap returned is not a zero-slot placeholder")
val _record = mimalloc_thread_init()
val heap = mimalloc_thread_heap()
expect(heap.pages_by_class.len()).to_be_greater_than(0)
```

</details>

### Thread heap independence

#### heaps start with all-empty page lists

- heaps start with all-empty page lists
   - Expected: all_empty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("heaps start with all-empty page lists")
val heap = mi_heap_new_thread()
var all_empty = true
for class_pages in heap.pages_by_class:
    if class_pages.len() != 0:
        all_empty = false
expect(all_empty).to_equal(true)
```

</details>

#### mi_heap_new_thread differs from a zero-page-slot heap

- mi_heap_new_thread differs from a zero-page-slot heap


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mi_heap_new_thread differs from a zero-page-slot heap")
val independent = mi_heap_new_thread()
val bare = MiHeap(size_classes: [], pages_by_class: [])
# Independent heap has slots; bare struct has none
expect(independent.pages_by_class.len()).to_be_greater_than(bare.pages_by_class.len())
```

</details>

### mimalloc_thread_destroy

#### destroy completes without error

- destroy completes without error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("destroy completes without error")
val record = mimalloc_thread_init()
expect(record.heap.pages_by_class.len()).to_be_greater_than(0)
mimalloc_thread_destroy()
val fallback = mimalloc_thread_heap()
expect(fallback.pages_by_class.len()).to_be_greater_than(0)
```

</details>

#### heap after destroy returns fallback with pre-built slots

- heap after destroy returns fallback with pre-built slots


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("heap after destroy returns fallback with pre-built slots")
val _record = mimalloc_thread_init()
mimalloc_thread_destroy()
val heap = mimalloc_thread_heap()
# After destroy the TLS slot is reset to sentinel (-1); the lookup
# falls back to mi_heap_new() which always returns a heap with slots.
expect(heap.pages_by_class.len()).to_be_greater_than(0)
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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7c27de93fda603a5fe14e12baef4047434d97f0820691d2aa88a2fc87901d387`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7c27de93fda603a5fe14e12baef4047434d97f0820691d2aa88a2fc87901d387`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7c27de93fda603a5fe14e12baef4047434d97f0820691d2aa88a2fc87901d387`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/alloc/mimalloc_tls_spec.spl
mirror: doc/06_spec/01_unit/lib/alloc/mimalloc_tls_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/alloc/mimalloc_tls_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/alloc/mimalloc_tls_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/alloc/mimalloc_tls_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/alloc/mimalloc_tls_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a heap with non-empty pages_by_class slots' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/alloc/mimalloc_tls_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returned heap size_classes is empty (slots built internally)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/alloc/mimalloc_tls_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two calls return independent heap values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
