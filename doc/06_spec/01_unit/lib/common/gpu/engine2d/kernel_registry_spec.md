# Kernel Registry Specification

> Tests covering kernel_size_bucket — boundary pixel counts map to stable buckets, kernel_slot_key — injective across op/bucket pairs, out-of-range rejected, kernel_table_new/register/lookup — round trip and seal interaction, span_batch_new/push/reset — lifecycle without growth, span_batch_execute — runs every pushed op via the scalar oracle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kernel Registry Specification

## Scenarios

### kernel_size_bucket — boundary pixel counts map to stable buckets

#### maps boundary pixel counts to stable buckets

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps boundary pixel counts to stable buckets


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps boundary pixel counts to stable buckets")
assert_true(kernel_size_bucket(0) == KERNEL_BUCKET_TINY)
assert_true(kernel_size_bucket(1) == KERNEL_BUCKET_TINY)
assert_true(kernel_size_bucket(15) == KERNEL_BUCKET_TINY)
assert_true(kernel_size_bucket(16) == KERNEL_BUCKET_SMALL)
assert_true(kernel_size_bucket(63) == KERNEL_BUCKET_SMALL)
assert_true(kernel_size_bucket(64) == KERNEL_BUCKET_MEDIUM)
assert_true(kernel_size_bucket(65) == KERNEL_BUCKET_MEDIUM)
assert_true(kernel_size_bucket(255) == KERNEL_BUCKET_MEDIUM)
assert_true(kernel_size_bucket(256) == KERNEL_BUCKET_LARGE)
assert_true(kernel_size_bucket(1000000) == KERNEL_BUCKET_LARGE)
```

</details>

### kernel_slot_key — injective across op/bucket pairs, out-of-range rejected

#### is injective across op/bucket pairs

- is injective across op/bucket pairs


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is injective across op/bucket pairs")
val k00 = kernel_slot_key(KERNEL_OP_FILL_CONST, KERNEL_FORMAT_ARGB8888_STRAIGHT,
                          KERNEL_ALIGN_UNKNOWN, KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_TINY)
val k01 = kernel_slot_key(KERNEL_OP_FILL_CONST, KERNEL_FORMAT_ARGB8888_STRAIGHT,
                          KERNEL_ALIGN_UNKNOWN, KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_SMALL)
val k10 = kernel_slot_key(KERNEL_OP_COPY_SPAN, KERNEL_FORMAT_ARGB8888_STRAIGHT,
                          KERNEL_ALIGN_UNKNOWN, KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_TINY)
val k00_dup = kernel_slot_key(KERNEL_OP_FILL_CONST, KERNEL_FORMAT_ARGB8888_STRAIGHT,
                              KERNEL_ALIGN_UNKNOWN, KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_TINY)
assert_true(k00 != k01)
assert_true(k00 != k10)
assert_true(k01 != k10)
assert_true(k00 == k00_dup)
```

</details>

#### returns -1 for any out-of-range axis rather than aliasing a valid slot

- returns -1 for any out-of-range axis rather than aliasing a valid slot


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 for any out-of-range axis rather than aliasing a valid slot")
assert_true(kernel_slot_key(0 - 1, 0, 0, 0, 0) == 0 - 1)
assert_true(kernel_slot_key(16, 0, 0, 0, 0) == 0 - 1)
assert_true(kernel_slot_key(0, 0 - 1, 0, 0, 0) == 0 - 1)
assert_true(kernel_slot_key(0, 4, 0, 0, 0) == 0 - 1)
assert_true(kernel_slot_key(0, 0, 0, 0, 4) == 0 - 1)
```

</details>

### kernel_table_new/register/lookup — round trip and seal interaction

#### starts every slot on scalar

- starts every slot on scalar


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts every slot on scalar")
var t = kernel_table_new()
assert_true(kernel_table_lookup(t, KERNEL_OP_FILL_CONST, KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                KERNEL_ALIGN_UNKNOWN, KERNEL_SPAN_CONTIGUOUS,
                                KERNEL_BUCKET_MEDIUM) == KERNEL_PROVIDER_SCALAR)
```

</details>

#### register-after-seal is rejected and lookup unchanged

- register-after-seal is rejected and lookup unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("register-after-seal is rejected and lookup unchanged")
var t = kernel_table_new()
kernel_table_seal(t)
val ok = kernel_table_register(t, KERNEL_OP_FILL_CONST, KERNEL_FORMAT_ARGB8888_STRAIGHT,
                               KERNEL_ALIGN_UNKNOWN, KERNEL_SPAN_CONTIGUOUS,
                               KERNEL_BUCKET_MEDIUM, SIMD_PROVIDER_ID, true, true)
assert_true(not ok)
assert_true(t.rejections == 1)
assert_true(kernel_table_lookup(t, KERNEL_OP_FILL_CONST, KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                KERNEL_ALIGN_UNKNOWN, KERNEL_SPAN_CONTIGUOUS,
                                KERNEL_BUCKET_MEDIUM) == KERNEL_PROVIDER_SCALAR)
```

</details>

#### lookup miss falls back to scalar, never nil, for an unregistered slot

- lookup miss falls back to scalar, never nil, for an unregistered slot


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lookup miss falls back to scalar, never nil, for an unregistered slot")
var t = kernel_table_new()
val provider = kernel_table_lookup(t, KERNEL_OP_COPY_SPAN, KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                   KERNEL_ALIGN_UNKNOWN, KERNEL_SPAN_CONTIGUOUS,
                                   KERNEL_BUCKET_LARGE)
assert_true(provider == KERNEL_PROVIDER_SCALAR)
```

</details>

#### lookup on an out-of-range key falls back to scalar without registering

- lookup on an out-of-range key falls back to scalar without registering


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lookup on an out-of-range key falls back to scalar without registering")
var t = kernel_table_new()
val provider = kernel_table_lookup(t, 0 - 1, 0, 0, 0, 0)
assert_true(provider == KERNEL_PROVIDER_SCALAR)
assert_true(t.lookups == 1)
```

</details>

### span_batch_new/push/reset — lifecycle without growth

#### push appends up to capacity, refuses on overflow, and reset empties for reuse

- push appends up to capacity, refuses on overflow, and reset empties for reuse


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("push appends up to capacity, refuses on overflow, and reset empties for reuse")
var b = span_batch_new(2)
val ok0 = span_batch_push(b, KERNEL_OP_FILL_CONST, 0, 0, 10, 0xFF00FF, 0)
val ok1 = span_batch_push(b, KERNEL_OP_COPY_SPAN, 10, 0, 5, 0, 0)
val ok2 = span_batch_push(b, KERNEL_OP_FILL_CONST, 20, 0, 3, 0, 0)
assert_true(ok0)
assert_true(ok1)
assert_true(not ok2)
assert_true(b.length == 2)
assert_true(b.overflow_refusals == 1)

span_batch_reset(b)
assert_true(b.length == 0)
val ok3 = span_batch_push(b, KERNEL_OP_FILL_CONST, 0, 0, 4, 0, 0)
assert_true(ok3)
assert_true(b.length == 1)
# capacity is unchanged by reset: a third push after one post-reset
# push still fits because reset freed the two prior slots.
val ok4 = span_batch_push(b, KERNEL_OP_FILL_CONST, 4, 0, 4, 0, 0)
assert_true(ok4)
assert_true(b.length == 2)
```

</details>

### span_batch_execute — runs every pushed op via the scalar oracle

#### executes all pushed ops and counts non-scalar lookups when a slot is registered

- executes all pushed ops and counts non-scalar lookups when a slot is registered


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes all pushed ops and counts non-scalar lookups when a slot is registered")
var table = kernel_table_new()
val reg_ok = kernel_table_register(table, KERNEL_OP_FILL_CONST, KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                   KERNEL_ALIGN_UNKNOWN, KERNEL_SPAN_CONTIGUOUS,
                                   KERNEL_BUCKET_TINY, SIMD_PROVIDER_ID, true, true)
assert_true(reg_ok)

var batch = span_batch_new(2)
span_batch_push(batch, KERNEL_OP_FILL_CONST, 0, 0, 4, 0xAABBCCDD, 0)
span_batch_push(batch, KERNEL_OP_COPY_SPAN, 4, 0, 4, 0, 0)

var dst: [u32] = [0; 8]
var src: [u32] = [0xAABBCCDD.to_u32(); 8]
var mask: [u32] = [0; 8]

val executed = span_batch_execute(batch, dst, src, mask, table,
                                  KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                  KERNEL_ALIGN_UNKNOWN, KERNEL_SPAN_CONTIGUOUS)
assert_true(executed == 2)
# op 0 (FILL_CONST, TINY bucket) was registered to SIMD_PROVIDER_ID above.
assert_true(batch.non_scalar_lookups == 1)
```

</details>

#### a zero-count op is skipped and not counted as executed

- a zero-count op is skipped and not counted as executed


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a zero-count op is skipped and not counted as executed")
var table = kernel_table_new()
var batch = span_batch_new(1)
span_batch_push(batch, KERNEL_OP_FILL_CONST, 0, 0, 0, 0, 0)
var dst: [u32] = [0; 4]
var src: [u32] = [0; 4]
var mask: [u32] = [0; 4]
val executed = span_batch_execute(batch, dst, src, mask, table,
                                  KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                  KERNEL_ALIGN_UNKNOWN, KERNEL_SPAN_CONTIGUOUS)
assert_true(executed == 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/gpu/engine2d/kernel_registry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering kernel_size_bucket — boundary pixel counts map to stable buckets, kernel_slot_key — injective across op/bucket pairs, out-of-range rejected, kernel_table_new/register/lookup — round trip and seal interaction, span_batch_new/push/reset — lifecycle without growth, span_batch_execute — runs every pushed op via the scalar oracle.
- kernel_size_bucket — boundary pixel counts map to stable buckets
- kernel_slot_key — injective across op/bucket pairs, out-of-range rejected
- kernel_table_new/register/lookup — round trip and seal interaction
- span_batch_new/push/reset — lifecycle without growth
- span_batch_execute — runs every pushed op via the scalar oracle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `831f60003d827792cadf2b4c301d11329cb9f9fe0ef383db6b3a1ea41a4e0314`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `831f60003d827792cadf2b4c301d11329cb9f9fe0ef383db6b3a1ea41a4e0314`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `831f60003d827792cadf2b4c301d11329cb9f9fe0ef383db6b3a1ea41a4e0314`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/gpu/engine2d/kernel_registry_spec.spl
mirror: doc/06_spec/01_unit/lib/common/gpu/engine2d/kernel_registry_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/gpu/engine2d/kernel_registry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/gpu/engine2d/kernel_registry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/gpu/engine2d/kernel_registry_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps boundary pixel counts to stable buckets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/gpu/engine2d/kernel_registry_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is injective across op/bucket pairs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/gpu/engine2d/kernel_registry_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns -1 for any out-of-range axis rather than aliasing a valid slot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
