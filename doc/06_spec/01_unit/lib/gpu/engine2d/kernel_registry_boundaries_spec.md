# Kernel Registry Boundaries Specification

> Tests covering kernel_size_bucket — true arm of each boundary if, not just the false fall-through, kernel_slot_key — true arm of every out-of-range axis check, isolated one at a time, kernel_table_register — key<0 short-circuit before the bit_exact/faster gate, kernel_table_lookup — key<0 short-circuit falls back to scalar without indexing slots, span_batch_push — true arm of the overflow refusal, scalar_oracle kernels — true arm of every count<=0 early return, scalar_oracle oracle_mask_src_over — false arm of the per-pixel m>0 check, simd_kernels detect_simd_level — true arm of the in-process cache hit.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kernel Registry Boundaries Specification

## Scenarios

### kernel_size_bucket — true arm of each boundary if, not just the false fall-through

#### takes the count<16 true branch for a below-threshold count

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- takes the count<16 true branch for a below-threshold count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("takes the count<16 true branch for a below-threshold count")
assert_true(kernel_size_bucket(5) == KERNEL_BUCKET_TINY)
```

</details>

#### takes the count<64 true branch once the count<16 check is false

- takes the count<64 true branch once the count<16 check is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("takes the count<64 true branch once the count<16 check is false")
assert_true(kernel_size_bucket(30) == KERNEL_BUCKET_SMALL)
```

</details>

#### takes the count<256 true branch once both earlier checks are false

- takes the count<256 true branch once both earlier checks are false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("takes the count<256 true branch once both earlier checks are false")
assert_true(kernel_size_bucket(100) == KERNEL_BUCKET_MEDIUM)
```

</details>

### kernel_slot_key — true arm of every out-of-range axis check, isolated one at a time

#### rejects an out-of-range op while every other axis is valid

- rejects an out-of-range op while every other axis is valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an out-of-range op while every other axis is valid")
val k = kernel_slot_key(0 - 1, KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
                        KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_TINY)
assert_true(k == 0 - 1)
```

</details>

#### rejects an out-of-range format once op is valid

- rejects an out-of-range format once op is valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an out-of-range format once op is valid")
val k = kernel_slot_key(KERNEL_OP_FILL_CONST, KERNEL_FORMAT_CAPACITY, KERNEL_ALIGN_UNKNOWN,
                        KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_TINY)
assert_true(k == 0 - 1)
```

</details>

#### rejects an out-of-range alignment once op and format are valid

- rejects an out-of-range alignment once op and format are valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an out-of-range alignment once op and format are valid")
val k = kernel_slot_key(KERNEL_OP_FILL_CONST, KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_CAPACITY,
                        KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_TINY)
assert_true(k == 0 - 1)
```

</details>

#### rejects an out-of-range contiguity once op/format/alignment are valid

- rejects an out-of-range contiguity once op/format/alignment are valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an out-of-range contiguity once op/format/alignment are valid")
val k = kernel_slot_key(KERNEL_OP_FILL_CONST, KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
                        KERNEL_CONTIGUITY_CAPACITY, KERNEL_BUCKET_TINY)
assert_true(k == 0 - 1)
```

</details>

#### rejects an out-of-range bucket once every earlier axis is valid

- rejects an out-of-range bucket once every earlier axis is valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an out-of-range bucket once every earlier axis is valid")
val k = kernel_slot_key(KERNEL_OP_FILL_CONST, KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
                        KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_CAPACITY)
assert_true(k == 0 - 1)
```

</details>

### kernel_table_register — key<0 short-circuit before the bit_exact/faster gate

#### rejects an out-of-range op before ever consulting bit_exact/faster

- rejects an out-of-range op before ever consulting bit_exact/faster


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an out-of-range op before ever consulting bit_exact/faster")
var t = kernel_table_new()
val ok = kernel_table_register(t, KERNEL_OP_CAPACITY, KERNEL_FORMAT_ARGB8888_STRAIGHT,
                               KERNEL_ALIGN_UNKNOWN, KERNEL_SPAN_CONTIGUOUS,
                               KERNEL_BUCKET_TINY, SIMD_PROVIDER_ID, true, true)
assert_true(not ok)
assert_true(t.rejections == 1)
```

</details>

### kernel_table_lookup — key<0 short-circuit falls back to scalar without indexing slots

#### falls back to scalar for an out-of-range op on lookup

- falls back to scalar for an out-of-range op on lookup


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to scalar for an out-of-range op on lookup")
var t = kernel_table_new()
val provider = kernel_table_lookup(t, KERNEL_OP_CAPACITY, KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                   KERNEL_ALIGN_UNKNOWN, KERNEL_SPAN_CONTIGUOUS,
                                   KERNEL_BUCKET_TINY)
assert_true(provider == KERNEL_PROVIDER_SCALAR)
```

</details>

### span_batch_push — true arm of the overflow refusal

#### refuses the push once length reaches capacity

- refuses the push once length reaches capacity


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses the push once length reaches capacity")
var b = span_batch_new(1)
val ok0 = span_batch_push(b, KERNEL_OP_FILL_CONST, 0, 0, 4, 0, 0)
val ok1 = span_batch_push(b, KERNEL_OP_FILL_CONST, 4, 0, 4, 0, 0)
assert_true(ok0)
assert_false(ok1)
assert_true(b.overflow_refusals == 1)
```

</details>

### scalar_oracle kernels — true arm of every count<=0 early return

#### oracle_fill_const returns immediately for a zero count, leaving dst untouched

- oracle_fill_const returns immediately for a zero count, leaving dst untouched


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("oracle_fill_const returns immediately for a zero count, leaving dst untouched")
var dst: [u32] = [0xAAAAAAAA.to_u32(); 4]
oracle_fill_const(dst, 0, 0, 0xFFFFFFFF)
assert_true(dst[0] == 0xAAAAAAAA.to_u32())
```

</details>

#### oracle_src_over_const returns immediately for a zero count

- oracle_src_over_const returns immediately for a zero count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("oracle_src_over_const returns immediately for a zero count")
var dst: [u32] = [0x11111111.to_u32(); 4]
oracle_src_over_const(dst, 0, 0, 0xFFFFFFFF)
assert_true(dst[0] == 0x11111111.to_u32())
```

</details>

#### oracle_src_over_image returns immediately for a zero count

- oracle_src_over_image returns immediately for a zero count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("oracle_src_over_image returns immediately for a zero count")
var dst: [u32] = [0x22222222.to_u32(); 4]
var src: [u32] = [0xFFFFFFFF.to_u32(); 4]
oracle_src_over_image(dst, 0, src, 0, 0)
assert_true(dst[0] == 0x22222222.to_u32())
```

</details>

#### oracle_mask_src_over returns immediately for a zero count

- oracle_mask_src_over returns immediately for a zero count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("oracle_mask_src_over returns immediately for a zero count")
var dst: [u32] = [0x33333333.to_u32(); 4]
var mask: [u32] = [0xFF.to_u32(); 4]
oracle_mask_src_over(dst, 0, 0xFFFFFFFF, mask, 0, 0)
assert_true(dst[0] == 0x33333333.to_u32())
```

</details>

#### oracle_hash_span returns the seed hash immediately for a zero count

- oracle_hash_span returns the seed hash immediately for a zero count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("oracle_hash_span returns the seed hash immediately for a zero count")
var buf: [u32] = [0xDEADBEEF.to_u32(); 4]
val h = oracle_hash_span(buf, 0, 0)
assert_true(h == (0xCBF29CE484222325 & 0xFFFFFFFFFFFF))
```

</details>

### scalar_oracle oracle_mask_src_over — false arm of the per-pixel m>0 check

#### skips a zero-coverage mask pixel without touching dst at that index

- skips a zero-coverage mask pixel without touching dst at that index


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips a zero-coverage mask pixel without touching dst at that index")
var dst: [u32] = [0x44444444.to_u32(); 2]
var mask: [u32] = [0.to_u32(), 0xFF.to_u32()]
oracle_mask_src_over(dst, 0, 0xFFFFFFFF, mask, 0, 2)
assert_true(dst[0] == 0x44444444.to_u32())
assert_true(dst[1] != 0x44444444.to_u32())
```

</details>

### simd_kernels detect_simd_level — true arm of the in-process cache hit

#### returns the same level on a second call without re-probing

- returns the same level on a second call without re-probing


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the same level on a second call without re-probing")
val first = detect_simd_level()
val second = detect_simd_level()
assert_true(first == second)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/kernel_registry_boundaries_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering kernel_size_bucket — true arm of each boundary if, not just the false fall-through, kernel_slot_key — true arm of every out-of-range axis check, isolated one at a time, kernel_table_register — key<0 short-circuit before the bit_exact/faster gate, kernel_table_lookup — key<0 short-circuit falls back to scalar without indexing slots, span_batch_push — true arm of the overflow refusal, scalar_oracle kernels — true arm of every count<=0 early return, scalar_oracle oracle_mask_src_over — false arm of the per-pixel m>0 check, simd_kernels detect_simd_level — true arm of the in-process cache hit.
- kernel_size_bucket — true arm of each boundary if, not just the false fall-through
- kernel_slot_key — true arm of every out-of-range axis check, isolated one at a time
- kernel_table_register — key<0 short-circuit before the bit_exact/faster gate
- kernel_table_lookup — key<0 short-circuit falls back to scalar without indexing slots
- span_batch_push — true arm of the overflow refusal
- scalar_oracle kernels — true arm of every count<=0 early return
- scalar_oracle oracle_mask_src_over — false arm of the per-pixel m>0 check
- simd_kernels detect_simd_level — true arm of the in-process cache hit

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `4294ec05e35f453461413616eaf23cc94fa51a516ff6913760ad1461ce63fb23`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4294ec05e35f453461413616eaf23cc94fa51a516ff6913760ad1461ce63fb23`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4294ec05e35f453461413616eaf23cc94fa51a516ff6913760ad1461ce63fb23`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gpu/engine2d/kernel_registry_boundaries_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/kernel_registry_boundaries_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/kernel_registry_boundaries_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/kernel_registry_boundaries_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/kernel_registry_boundaries_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'takes the count<16 true branch for a below-threshold count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/kernel_registry_boundaries_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'takes the count<64 true branch once the count<16 check is false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/kernel_registry_boundaries_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'takes the count<256 true branch once both earlier checks are false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
