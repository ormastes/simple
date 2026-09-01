# Packed Span Specification

> Tests covering packed span registry (F2), packed span counted refusal gate (F2), packed span native resolve ABI (F2, SimplePackedSpanV1).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Packed Span Specification

## Scenarios

### packed span registry (F2)

#### resolves a valid in-bounds span

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves a valid in-bounds span


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a valid in-bounds span")
val reg = PackedSpanRegistry.create(4)
val slot = reg.register(4096)
assert_true(slot >= 0)
val gen = reg.generation_of(slot)
val r = packed_span_make(slot, gen, 0, 1024, 4)
assert_true(reg.resolve(r) == PACKED_SPAN_OK)
```

</details>

#### resolves an offset window inside the buffer

- resolves an offset window inside the buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves an offset window inside the buffer")
val reg = PackedSpanRegistry.create(4)
val slot = reg.register(4096)
val r = packed_span_make(slot, reg.generation_of(slot), 2048, 512, 4)
assert_true(reg.resolve(r) == PACKED_SPAN_OK)
```

</details>

#### refuses a stale generation after invalidate

- refuses a stale generation after invalidate


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a stale generation after invalidate")
val reg = PackedSpanRegistry.create(4)
val slot = reg.register(4096)
val r = packed_span_make(slot, reg.generation_of(slot), 0, 8, 4)
assert_true(reg.invalidate(slot))
assert_true(reg.resolve(r) == PACKED_SPAN_STALE_GENERATION)
```

</details>

#### refuses a wrong generation even on a live slot

- refuses a wrong generation even on a live slot


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a wrong generation even on a live slot")
val reg = PackedSpanRegistry.create(4)
val slot = reg.register(64)
val r = packed_span_make(slot, reg.generation_of(slot) + 1, 0, 4, 4)
assert_true(reg.resolve(r) == PACKED_SPAN_STALE_GENERATION)
```

</details>

#### refuses an unknown slot

- refuses an unknown slot


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an unknown slot")
val reg = PackedSpanRegistry.create(2)
val r = packed_span_make(7, 1, 0, 4, 4)
assert_true(reg.resolve(r) == PACKED_SPAN_BAD_SLOT)
```

</details>

#### refuses a window past the end of the buffer

- refuses a window past the end of the buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a window past the end of the buffer")
val reg = PackedSpanRegistry.create(2)
val slot = reg.register(100)
val r = packed_span_make(slot, reg.generation_of(slot), 96, 2, 4)
assert_true(reg.resolve(r) == PACKED_SPAN_OUT_OF_BOUNDS)
```

</details>

#### refuses a zero stride

- refuses a zero stride


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a zero stride")
val reg = PackedSpanRegistry.create(2)
val slot = reg.register(64)
val bad = BufferSpanRef(object_slot: slot as u32, object_generation: reg.generation_of(slot), byte_offset: 0, byte_length: 16, element_count: 16, element_stride: 0)
assert_true(reg.resolve(bad) == PACKED_SPAN_BAD_STRIDE)
```

</details>

#### refuses a count*stride / byte_length mismatch

- refuses a count*stride / byte_length mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a count*stride / byte_length mismatch")
val reg = PackedSpanRegistry.create(2)
val slot = reg.register(64)
val bad = BufferSpanRef(object_slot: slot as u32, object_generation: reg.generation_of(slot), byte_offset: 0, byte_length: 15, element_count: 4, element_stride: 4)
assert_true(reg.resolve(bad) == PACKED_SPAN_BAD_STRIDE)
```

</details>

#### reports an empty span as empty, not ok

- reports an empty span as empty, not ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports an empty span as empty, not ok")
val reg = PackedSpanRegistry.create(2)
val slot = reg.register(64)
val r = packed_span_make(slot, reg.generation_of(slot), 0, 0, 4)
assert_true(reg.resolve(r) == PACKED_SPAN_EMPTY)
```

</details>

#### fails closed when the registry is full

- fails closed when the registry is full


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when the registry is full")
val reg = PackedSpanRegistry.create(1)
assert_true(reg.register(16) == 0)
assert_true(reg.register(16) == -1)
```

</details>

### packed span counted refusal gate (F2)

#### counts a refusal instead of returning a silent zero

- counts a refusal instead of returning a silent zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts a refusal instead of returning a silent zero")
val reg = PackedSpanRegistry.create(2)
val slot = reg.register(4096)
val r = packed_span_make(slot, reg.generation_of(slot), 0, 8, 4)
assert_true(reg.invalidate(slot))
val verdict = reg.resolve(r)
# A silent-zero failure would report OK (0) here.
assert_true(verdict == PACKED_SPAN_STALE_GENERATION)
assert_equal(reg.rejected_op_count, 1)
assert_equal(reg.last_rejection, PACKED_SPAN_STALE_GENERATION)
# A refused batch must admit ZERO elements.
assert_equal(reg.admitted_element_count, 0)
```

</details>

#### does not count a successful resolve as a rejection

- does not count a successful resolve as a rejection


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not count a successful resolve as a rejection")
val reg = PackedSpanRegistry.create(2)
val slot = reg.register(4096)
val r = packed_span_make(slot, reg.generation_of(slot), 0, 64, 4)
assert_true(reg.resolve(r) == PACKED_SPAN_OK)
assert_equal(reg.rejected_op_count, 0)
assert_equal(reg.last_rejection, PACKED_SPAN_OK)
assert_equal(reg.admitted_element_count, 64)
```

</details>

#### accumulates each distinct refusal kind and keeps the latest

- accumulates each distinct refusal kind and keeps the latest


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accumulates each distinct refusal kind and keeps the latest")
val reg = PackedSpanRegistry.create(2)
val slot = reg.register(64)
assert_true(reg.resolve(packed_span_make(9, 1, 0, 4, 4)) == PACKED_SPAN_BAD_SLOT)
assert_equal(reg.last_rejection, PACKED_SPAN_BAD_SLOT)
assert_true(reg.resolve(packed_span_make(slot, reg.generation_of(slot), 60, 2, 4)) == PACKED_SPAN_OUT_OF_BOUNDS)
assert_equal(reg.last_rejection, PACKED_SPAN_OUT_OF_BOUNDS)
assert_equal(reg.rejected_op_count, 2)
assert_equal(reg.resolve_call_count, 2)
```

</details>

#### performs exactly ONE check for a whole submitted batch

- performs exactly ONE check for a whole submitted batch


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("performs exactly ONE check for a whole submitted batch")
val reg = PackedSpanRegistry.create(2)
val slot = reg.register(65536)
val r = packed_span_make(slot, reg.generation_of(slot), 0, 16384, 4)
assert_true(reg.resolve(r) == PACKED_SPAN_OK)
# 16384 elements admitted against 1 gate call — a per-element gate
# would make these two numbers equal.
assert_equal(reg.resolve_call_count, 1)
assert_equal(reg.admitted_element_count, 16384)
```

</details>

#### leaves the counters untouched when probing with check

- leaves the counters untouched when probing with check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves the counters untouched when probing with check")
val reg = PackedSpanRegistry.create(2)
val slot = reg.register(64)
val bad = packed_span_make(slot, reg.generation_of(slot) + 5, 0, 4, 4)
assert_true(reg.check(bad) == PACKED_SPAN_STALE_GENERATION)
assert_equal(reg.resolve_call_count, 0)
assert_equal(reg.rejected_op_count, 0)
```

</details>

#### reports a backend it can actually deliver, never a bare capability bit

- reports a backend it can actually deliver, never a bare capability bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a backend it can actually deliver, never a bare capability bit")
# MEASURED, not asserted: packed_span_backend_name() probes the C
# resolve live and only claims "native-packed-v1" when the engine
# actually hands back a non-zero base. The tree-walk interpreter boxes
# [u8] elements and has no contiguous buffer, so it stays on the
# scalar oracle -- and says so.
val name = packed_span_backend_name()
assert_true(name == "scalar-oracle" or name == "native-packed-v1")
val reg = PackedSpanRegistry.create(2)
val slot = reg.register(64)
val r = packed_span_make(slot, reg.generation_of(slot), 0, 16, 4)
assert_true(reg.resolve(r) == PACKED_SPAN_OK)
val resolved = packed_span_resolve_base(packed_span_probe_bytes(64), r)
match resolved:
    case Ok(base):
        assert_equal(name, "native-packed-v1")
        assert_true(base != 0)
    case Err(verdict):
        assert_equal(name, "scalar-oracle")
        # A refusal is carried by the result, never inferred from 0.
        assert_equal(verdict, PACKED_SPAN_C_NO_BASE)
        assert_equal(packed_span_last_verdict(), verdict)
```

</details>

### packed span native resolve ABI (F2, SimplePackedSpanV1)

#### pins the SimplePackedSpanV1 ABI width at 40 bytes

- pins the SimplePackedSpanV1 ABI width at 40 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins the SimplePackedSpanV1 ABI width at 40 bytes")
# magic-first, LP64, no padding holes. A silent layout change here
# would silently change what every caller reads.
assert_equal(packed_span_abi_struct_size(), 40)
```

</details>

#### refuses a backing that is not a bytes basis, and counts it

- refuses a backing that is not a bytes basis, and counts it


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a backing that is not a bytes basis, and counts it")
# [u32] / rt_typed_words_u32_* are 8-byte-stride, value-tagged storage
# and are NOT a packed pixel basis. Never a silent cast.
val before = packed_span_rejected_count()
# basis_len < 0 == "not a bytes basis".
assert_equal(packed_span_probe_verdict(-1, 0, 16, 4, 4), PACKED_SPAN_C_WRONG_BASIS)
assert_equal(packed_span_last_verdict(), PACKED_SPAN_C_WRONG_BASIS)
assert_equal(packed_span_rejected_count() - before, 1)
```

</details>

#### refuses a window one byte past the end, and counts it

- refuses a window one byte past the end, and counts it


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a window one byte past the end, and counts it")
val before = packed_span_rejected_count()
assert_equal(packed_span_probe_verdict(4096, 1, 4096, 1024, 4), PACKED_SPAN_C_OUT_OF_BOUNDS)
assert_equal(packed_span_last_verdict(), PACKED_SPAN_C_OUT_OF_BOUNDS)
assert_equal(packed_span_rejected_count() - before, 1)
```

</details>

#### refuses count * stride != byte_length, and counts it

- refuses count * stride != byte_length, and counts it


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses count * stride != byte_length, and counts it")
val before = packed_span_rejected_count()
assert_equal(packed_span_probe_verdict(4096, 0, 4096, 1000, 4), PACKED_SPAN_C_BAD_STRIDE)
assert_equal(packed_span_last_verdict(), PACKED_SPAN_C_BAD_STRIDE)
assert_equal(packed_span_rejected_count() - before, 1)
```

</details>

#### refuses a zero stride rather than dividing by it

- refuses a zero stride rather than dividing by it


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a zero stride rather than dividing by it")
val before = packed_span_rejected_count()
assert_equal(packed_span_probe_verdict(4096, 0, 4096, 1024, 0), PACKED_SPAN_C_BAD_STRIDE)
assert_equal(packed_span_rejected_count() - before, 1)
```

</details>

#### refuses an empty window rather than returning a zero-length OK span

- refuses an empty window rather than returning a zero-length OK span


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an empty window rather than returning a zero-length OK span")
val before = packed_span_rejected_count()
assert_equal(packed_span_probe_verdict(64, 0, 0, 0, 4), PACKED_SPAN_C_EMPTY)
assert_equal(packed_span_last_verdict(), PACKED_SPAN_C_EMPTY)
assert_equal(packed_span_rejected_count() - before, 1)
```

</details>

#### never returns OK without a base -- the no-base path is typed

- never returns OK without a base -- the no-base path is typed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never returns OK without a base -- the no-base path is typed")
# A structurally perfect window with no backing pointer is still a
# refusal (-7), never a zero-address success.
assert_equal(packed_span_probe_verdict(4096, 0, 4096, 1024, 4), PACKED_SPAN_C_NO_BASE)
```

</details>

#### never reaches C for a stale generation -- the registry refuses first

- never reaches C for a stale generation -- the registry refuses first


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never reaches C for a stale generation -- the registry refuses first")
# Clause 5: generation lifetime is a language-level ownership fact,
# so C never sees object_slot / object_generation. The proof is that
# the C refusal counter does not move.
val reg = PackedSpanRegistry.create(2)
val slot = reg.register(4096)
val r = packed_span_make(slot, reg.generation_of(slot), 0, 1024, 4)
assert_true(reg.invalidate(slot))
val c_before = packed_span_rejected_count()
assert_true(reg.resolve(r) == PACKED_SPAN_STALE_GENERATION)
assert_equal(packed_span_rejected_count() - c_before, 0)
```

</details>

#### keeps the two halves of the one batch check on their own sides

- keeps the two halves of the one batch check on their own sides


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the two halves of the one batch check on their own sides")
# The registry adjudicates ownership; C adjudicates memory. Together
# they are ONE check for the whole batch -- 16384 elements admitted
# against a single registry gate call.
val reg = PackedSpanRegistry.create(2)
val slot = reg.register(65536)
val r = packed_span_make(slot, reg.generation_of(slot), 0, 16384, 4)
assert_true(reg.resolve(r) == PACKED_SPAN_OK)
assert_equal(reg.resolve_call_count, 1)
assert_equal(reg.admitted_element_count, 16384)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/memory/packed_span_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering packed span registry (F2), packed span counted refusal gate (F2), packed span native resolve ABI (F2, SimplePackedSpanV1).
- packed span registry (F2)
- packed span counted refusal gate (F2)
- packed span native resolve ABI (F2, SimplePackedSpanV1)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
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

- Canonical SPipe generation for source `06e93cad4faa70383defda249a55c7f5c3cee7d95689c35fc37ec401cb4b6a54`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `06e93cad4faa70383defda249a55c7f5c3cee7d95689c35fc37ec401cb4b6a54`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `06e93cad4faa70383defda249a55c7f5c3cee7d95689c35fc37ec401cb4b6a54`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/memory/packed_span_spec.spl
mirror: doc/06_spec/01_unit/lib/common/memory/packed_span_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/memory/packed_span_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/memory/packed_span_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/memory/packed_span_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a valid in-bounds span' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/memory/packed_span_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves an offset window inside the buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/memory/packed_span_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a stale generation after invalidate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
