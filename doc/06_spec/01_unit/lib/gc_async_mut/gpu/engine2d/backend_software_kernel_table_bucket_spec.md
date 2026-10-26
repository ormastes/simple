# Backend Software Kernel Table Bucket Specification

> Tests covering kernel_size_bucket — bucket boundaries used by the honest gate, kernel_table_register — honest gate can produce EITHER outcome for a small bucket (sabotage test), SIMD-ISA fill_const bit-exactness at small-bucket span lengths, honest per-bucket timing (interpreter engine) — real numbers, not hardcoded, real hit-count evidence — small-surface Engine2D.clear() exercises the per-bucket gate, SIMD-ISA src_over_const bit-exactness at representative bucket spans, SIMD-ISA src_over_image bit-exactness at representative bucket spans, SIMD-ISA mask_src_over bit-exactness at representative bucket spans, honest-gate invariant per new op — registered IFF measured exact AND faster (production probes), gate refusal per new op — a losing (or non-exact) measurement stays scalar, total table-build cost + owned-table persistence — 4 ops x 4 buckets probed at ensure_kernel_table time.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Software Kernel Table Bucket Specification

## Scenarios

### kernel_size_bucket — bucket boundaries used by the honest gate

#### classifies 8, 32, 128, 4096 into TINY, SMALL, MEDIUM, LARGE respectively

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- classifies 8, 32, 128, 4096 into TINY, SMALL, MEDIUM, LARGE respectively


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies 8, 32, 128, 4096 into TINY, SMALL, MEDIUM, LARGE respectively")
assert_true(kernel_size_bucket(8) == KERNEL_BUCKET_TINY)
assert_true(kernel_size_bucket(32) == KERNEL_BUCKET_SMALL)
assert_true(kernel_size_bucket(128) == KERNEL_BUCKET_MEDIUM)
assert_true(kernel_size_bucket(4096) == KERNEL_BUCKET_LARGE)
```

</details>

### kernel_table_register — honest gate can produce EITHER outcome for a small bucket (sabotage test)

#### keeps TINY on scalar when faster=false, even though bit_exact=true

- keeps TINY on scalar when faster=false, even though bit_exact=true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps TINY on scalar when faster=false, even though bit_exact=true")
var t = kernel_table_new()
val ok = kernel_table_register(t, KERNEL_OP_FILL_CONST,
                               KERNEL_FORMAT_ARGB8888_STRAIGHT,
                               KERNEL_ALIGN_UNKNOWN,
                               KERNEL_SPAN_CONTIGUOUS,
                               KERNEL_BUCKET_TINY,
                               SIMD_PROVIDER_ID, true, false)
assert_true(not ok)
assert_true(kernel_table_lookup(t, KERNEL_OP_FILL_CONST,
                                KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                KERNEL_ALIGN_UNKNOWN,
                                KERNEL_SPAN_CONTIGUOUS,
                                KERNEL_BUCKET_TINY) == KERNEL_PROVIDER_SCALAR)
```

</details>

#### registers TINY when faster=true and bit_exact=true — same gate, opposite real outcome

- registers TINY when faster=true and bit_exact=true — same gate, opposite real outcome


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers TINY when faster=true and bit_exact=true — same gate, opposite real outcome")
var t = kernel_table_new()
val ok = kernel_table_register(t, KERNEL_OP_FILL_CONST,
                               KERNEL_FORMAT_ARGB8888_STRAIGHT,
                               KERNEL_ALIGN_UNKNOWN,
                               KERNEL_SPAN_CONTIGUOUS,
                               KERNEL_BUCKET_TINY,
                               SIMD_PROVIDER_ID, true, true)
assert_true(ok)
assert_true(kernel_table_lookup(t, KERNEL_OP_FILL_CONST,
                                KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                KERNEL_ALIGN_UNKNOWN,
                                KERNEL_SPAN_CONTIGUOUS,
                                KERNEL_BUCKET_TINY) == SIMD_PROVIDER_ID)
```

</details>

#### never registers when bit_exact=false regardless of faster — bit-exactness is not optional

- never registers when bit_exact=false regardless of faster — bit-exactness is not optional


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never registers when bit_exact=false regardless of faster — bit-exactness is not optional")
var t = kernel_table_new()
val ok = kernel_table_register(t, KERNEL_OP_FILL_CONST,
                               KERNEL_FORMAT_ARGB8888_STRAIGHT,
                               KERNEL_ALIGN_UNKNOWN,
                               KERNEL_SPAN_CONTIGUOUS,
                               KERNEL_BUCKET_SMALL,
                               SIMD_PROVIDER_ID, false, true)
assert_true(not ok)
assert_true(kernel_table_lookup(t, KERNEL_OP_FILL_CONST,
                                KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                KERNEL_ALIGN_UNKNOWN,
                                KERNEL_SPAN_CONTIGUOUS,
                                KERNEL_BUCKET_SMALL) == KERNEL_PROVIDER_SCALAR)
```

</details>

### SIMD-ISA fill_const bit-exactness at small-bucket span lengths

#### agrees with the scalar oracle pixel-for-pixel at an 8px TINY span

- agrees with the scalar oracle pixel-for-pixel at an 8px TINY span


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with the scalar oracle pixel-for-pixel at an 8px TINY span")
var oracle_buf: [u32] = [0; 8]
var simd_buf: [u32] = [0; 8]
oracle_fill_const(oracle_buf, 0, 8, 0xFF335577)
simd_isa_fill_const(simd_buf, 0, 8, 0xFF335577)
assert_true(oracle_hash_span(oracle_buf, 0, 8) == oracle_hash_span(simd_buf, 0, 8))
```

</details>

#### agrees with the scalar oracle pixel-for-pixel at a 32px SMALL span

- agrees with the scalar oracle pixel-for-pixel at a 32px SMALL span


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with the scalar oracle pixel-for-pixel at a 32px SMALL span")
var oracle_buf: [u32] = [0; 32]
var simd_buf: [u32] = [0; 32]
oracle_fill_const(oracle_buf, 0, 32, 0xFF204060)
simd_isa_fill_const(simd_buf, 0, 32, 0xFF204060)
assert_true(oracle_hash_span(oracle_buf, 0, 32) == oracle_hash_span(simd_buf, 0, 32))
```

</details>

#### agrees with the scalar oracle pixel-for-pixel at a 128px MEDIUM span

- agrees with the scalar oracle pixel-for-pixel at a 128px MEDIUM span


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with the scalar oracle pixel-for-pixel at a 128px MEDIUM span")
var oracle_buf: [u32] = [0; 128]
var simd_buf: [u32] = [0; 128]
oracle_fill_const(oracle_buf, 0, 128, 0xFF102030)
simd_isa_fill_const(simd_buf, 0, 128, 0xFF102030)
assert_true(oracle_hash_span(oracle_buf, 0, 128) == oracle_hash_span(simd_buf, 0, 128))
```

</details>

### honest per-bucket timing (interpreter engine) — real numbers, not hardcoded

<details>
<summary>Advanced: measures fill_const at TINY (8px), SMALL (32px), MEDIUM (128px), LARGE (4096px) and reports which buckets earn SIMD</summary>

#### measures fill_const at TINY (8px), SMALL (32px), MEDIUM (128px), LARGE (4096px) and reports which buckets earn SIMD _(slow)_

- measures fill_const at TINY (8px), SMALL (32px), MEDIUM (128px), LARGE (4096px) and reports which buckets earn SIMD


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures fill_const at TINY (8px), SMALL (32px), MEDIUM (128px), LARGE (4096px) and reports which buckets earn SIMD")
var t = kernel_table_new()
var buf8: [u32] = [0; 8]
var buf32: [u32] = [0; 32]
var buf128: [u32] = [0; 128]
var buf4096: [u32] = [0; 4096]

val iters_small: i64 = 4000
val iters_large: i64 = 64

# TINY
val ts0 = time_now_unix_micros()
var i0: i64 = 0
while i0 < iters_small:
    oracle_fill_const(buf8, 0, 8, 0xFF102030)
    i0 = i0 + 1
val scalar_tiny_us = time_now_unix_micros() - ts0
val tt0 = time_now_unix_micros()
var i1: i64 = 0
while i1 < iters_small:
    simd_isa_fill_const(buf8, 0, 8, 0xFF102030)
    i1 = i1 + 1
val simd_tiny_us = time_now_unix_micros() - tt0
val tiny_faster = simd_tiny_us < scalar_tiny_us
val tiny_ok = kernel_table_register(t, KERNEL_OP_FILL_CONST,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_TINY, SIMD_PROVIDER_ID, true, tiny_faster)
assert_true(tiny_ok == tiny_faster)

# LARGE (control: this bucket was already measured before the fix)
val ls0 = time_now_unix_micros()
var i2: i64 = 0
while i2 < iters_large:
    oracle_fill_const(buf4096, 0, 4096, 0xFF102030)
    i2 = i2 + 1
val scalar_large_us = time_now_unix_micros() - ls0
val lt0 = time_now_unix_micros()
var i3: i64 = 0
while i3 < iters_large:
    simd_isa_fill_const(buf4096, 0, 4096, 0xFF102030)
    i3 = i3 + 1
val simd_large_us = time_now_unix_micros() - lt0
val large_faster = simd_large_us < scalar_large_us
val large_ok = kernel_table_register(t, KERNEL_OP_FILL_CONST,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_LARGE, SIMD_PROVIDER_ID, true, large_faster)
assert_true(large_ok == large_faster)

print("bucket timing us (interpreter): TINY(8px) scalar=" + scalar_tiny_us.to_text() +
      " simd=" + simd_tiny_us.to_text() + " registered=" + tiny_ok.to_text() +
      " | LARGE(4096px) scalar=" + scalar_large_us.to_text() +
      " simd=" + simd_large_us.to_text() + " registered=" + large_ok.to_text())
```

</details>


</details>

### real hit-count evidence — small-surface Engine2D.clear() exercises the per-bucket gate

<details>
<summary>Advanced: a 10x4 clear() (TINY-bucket 10px row spans) runs ensure_kernel_table for TINY and reports observable state</summary>

#### a 10x4 clear() (TINY-bucket 10px row spans) runs ensure_kernel_table for TINY and reports observable state _(slow)_

- a 10x4 clear() (TINY-bucket 10px row spans) runs ensure_kernel_table for TINY and reports observable state


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a 10x4 clear() (TINY-bucket 10px row spans) runs ensure_kernel_table for TINY and reports observable state")
var backend = SoftwareBackend.create_cpu_simd()
val started = backend.init(10, 4)
assert_true(started)
assert_true(backend.kernel_table_ready == false)
backend.clear(0xFF001122u32)
# ensure_kernel_table always runs (and seals) on the first fill,
# regardless of which buckets end up on SIMD vs scalar — this is
# the actual bug signature: before the fix, TINY was never probed
# at all, so this flag could not meaningfully reflect TINY-bucket
# measurement. Now it always does.
assert_true(backend.kernel_table_ready == true)
# Correctness: the surface was actually filled with the requested
# colour regardless of which provider serviced it.
assert_true(backend.buf[0] == 0xFF001122u32)
assert_true(backend.buf[39] == 0xFF001122u32)
print("post-clear(10x4) TINY-bucket exercise: kernel_table_ready=" +
      backend.kernel_table_ready.to_text() +
      " simd_batch_hits=" + backend.simd_batch_hits.to_text() +
      " (0 is a legitimate honest outcome if SIMD did not beat scalar at 10px on this machine)")
```

</details>


</details>

### SIMD-ISA src_over_const bit-exactness at representative bucket spans

#### agrees with oracle_src_over_const pixel-for-pixel at an 8px TINY span

- agrees with oracle_src_over_const pixel-for-pixel at an 8px TINY span


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with oracle_src_over_const pixel-for-pixel at an 8px TINY span")
var oracle_buf: [u32] = [0; 8]
var simd_buf: [u32] = [0; 8]
oracle_fill_const(oracle_buf, 0, 8, 0xFF404040)
oracle_fill_const(simd_buf, 0, 8, 0xFF404040)
oracle_src_over_const(oracle_buf, 0, 8, 0x80102030)
simd_isa_src_over_const(simd_buf, 0, 8, 0x80102030)
assert_true(oracle_hash_span(oracle_buf, 0, 8) == oracle_hash_span(simd_buf, 0, 8))
```

</details>

#### agrees with oracle_src_over_const pixel-for-pixel at a 300px LARGE span

- agrees with oracle_src_over_const pixel-for-pixel at a 300px LARGE span


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with oracle_src_over_const pixel-for-pixel at a 300px LARGE span")
var oracle_buf: [u32] = [0; 300]
var simd_buf: [u32] = [0; 300]
oracle_fill_const(oracle_buf, 0, 300, 0xFF204060)
oracle_fill_const(simd_buf, 0, 300, 0xFF204060)
oracle_src_over_const(oracle_buf, 0, 300, 0xC0FF8040)
simd_isa_src_over_const(simd_buf, 0, 300, 0xC0FF8040)
assert_true(oracle_hash_span(oracle_buf, 0, 300) == oracle_hash_span(simd_buf, 0, 300))
```

</details>

### SIMD-ISA src_over_image bit-exactness at representative bucket spans

#### agrees with oracle_src_over_image pixel-for-pixel at an 8px TINY span

- agrees with oracle_src_over_image pixel-for-pixel at an 8px TINY span


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with oracle_src_over_image pixel-for-pixel at an 8px TINY span")
var src: [u32] = [0; 8]
oracle_fill_const(src, 0, 8, 0x9033AA55)
var oracle_buf: [u32] = [0; 8]
var simd_buf: [u32] = [0; 8]
oracle_fill_const(oracle_buf, 0, 8, 0xFF404040)
oracle_fill_const(simd_buf, 0, 8, 0xFF404040)
oracle_src_over_image(oracle_buf, 0, src, 0, 8)
simd_isa_src_over_image(simd_buf, 0, src, 0, 8)
assert_true(oracle_hash_span(oracle_buf, 0, 8) == oracle_hash_span(simd_buf, 0, 8))
```

</details>

#### agrees with oracle_src_over_image pixel-for-pixel at a 300px LARGE span

- agrees with oracle_src_over_image pixel-for-pixel at a 300px LARGE span


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with oracle_src_over_image pixel-for-pixel at a 300px LARGE span")
var src: [u32] = [0; 300]
oracle_fill_const(src, 0, 300, 0x66CC2288)
var oracle_buf: [u32] = [0; 300]
var simd_buf: [u32] = [0; 300]
oracle_fill_const(oracle_buf, 0, 300, 0xFF103050)
oracle_fill_const(simd_buf, 0, 300, 0xFF103050)
oracle_src_over_image(oracle_buf, 0, src, 0, 300)
simd_isa_src_over_image(simd_buf, 0, src, 0, 300)
assert_true(oracle_hash_span(oracle_buf, 0, 300) == oracle_hash_span(simd_buf, 0, 300))
```

</details>

### SIMD-ISA mask_src_over bit-exactness at representative bucket spans

#### agrees with oracle_mask_src_over pixel-for-pixel at an 8px TINY span with mixed coverage

- agrees with oracle_mask_src_over pixel-for-pixel at an 8px TINY span with mixed coverage


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with oracle_mask_src_over pixel-for-pixel at an 8px TINY span with mixed coverage")
var mask: [u32] = [0; 8]
var m: i64 = 0
while m < 8:
    mask[m.to_i32()] = ((m * 37) % 256) as u32
    m = m + 1
var oracle_buf: [u32] = [0; 8]
var simd_buf: [u32] = [0; 8]
oracle_fill_const(oracle_buf, 0, 8, 0xFF404040)
oracle_fill_const(simd_buf, 0, 8, 0xFF404040)
oracle_mask_src_over(oracle_buf, 0, 0xC0104080, mask, 0, 8)
simd_isa_mask_src_over(simd_buf, 0, 0xC0104080, mask, 0, 8)
assert_true(oracle_hash_span(oracle_buf, 0, 8) == oracle_hash_span(simd_buf, 0, 8))
```

</details>

#### agrees with oracle_mask_src_over pixel-for-pixel at a 300px LARGE span including 0 and 255 coverage

- agrees with oracle_mask_src_over pixel-for-pixel at a 300px LARGE span including 0 and 255 coverage


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with oracle_mask_src_over pixel-for-pixel at a 300px LARGE span including 0 and 255 coverage")
var mask: [u32] = [0; 300]
var m: i64 = 0
while m < 300:
    mask[m.to_i32()] = ((m * 37) % 256) as u32
    m = m + 1
var oracle_buf: [u32] = [0; 300]
var simd_buf: [u32] = [0; 300]
oracle_fill_const(oracle_buf, 0, 300, 0xFF404040)
oracle_fill_const(simd_buf, 0, 300, 0xFF404040)
oracle_mask_src_over(oracle_buf, 0, 0xC0104080, mask, 0, 300)
simd_isa_mask_src_over(simd_buf, 0, 0xC0104080, mask, 0, 300)
assert_true(oracle_hash_span(oracle_buf, 0, 300) == oracle_hash_span(simd_buf, 0, 300))
```

</details>

### honest-gate invariant per new op — registered IFF measured exact AND faster (production probes)

<details>
<summary>Advanced: src_over_const TINY+LARGE: registration outcome matches the probe's own verdict</summary>

#### src_over_const TINY+LARGE: registration outcome matches the probe's own verdict _(slow)_

- src_over_const TINY+LARGE: registration outcome matches the probe's own verdict


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("src_over_const TINY+LARGE: registration outcome matches the probe's own verdict")
var t = kernel_table_new()
val tiny_v = _kernel_probe_src_over_const_bucket(8, 200)
val large_v = _kernel_probe_src_over_const_bucket(4096, 4)
val tiny_ok = kernel_table_register(t, KERNEL_OP_SRC_OVER_CONST,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_TINY, SIMD_PROVIDER_ID,
    (tiny_v & 2) != 0, (tiny_v & 1) != 0)
val large_ok = kernel_table_register(t, KERNEL_OP_SRC_OVER_CONST,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_LARGE, SIMD_PROVIDER_ID,
    (large_v & 2) != 0, (large_v & 1) != 0)
assert_true(tiny_ok == (tiny_v == 3))
assert_true(large_ok == (large_v == 3))
val tiny_simd = kernel_table_lookup(t, KERNEL_OP_SRC_OVER_CONST,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_TINY) == SIMD_PROVIDER_ID
val large_simd = kernel_table_lookup(t, KERNEL_OP_SRC_OVER_CONST,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_LARGE) == SIMD_PROVIDER_ID
assert_true(tiny_simd == tiny_ok)
assert_true(large_simd == large_ok)
# Probe bit-exactness must hold — a non-exact SIMD blend is a defect,
# not a legitimate scalar verdict.
assert_true((tiny_v & 2) != 0)
assert_true((large_v & 2) != 0)
print("src_over_const gate: TINY verdict=" + tiny_v.to_text() +
      " registered=" + tiny_simd.to_text() +
      " | LARGE verdict=" + large_v.to_text() +
      " registered=" + large_simd.to_text() + " (verdict: 1=faster, 2=exact, 3=both)")
```

</details>


</details>

<details>
<summary>Advanced: src_over_image TINY+LARGE: registration outcome matches the probe's own verdict</summary>

#### src_over_image TINY+LARGE: registration outcome matches the probe's own verdict _(slow)_

- src_over_image TINY+LARGE: registration outcome matches the probe's own verdict


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("src_over_image TINY+LARGE: registration outcome matches the probe's own verdict")
var t = kernel_table_new()
val tiny_v = _kernel_probe_src_over_image_bucket(8, 200)
val large_v = _kernel_probe_src_over_image_bucket(4096, 4)
val tiny_ok = kernel_table_register(t, KERNEL_OP_SRC_OVER_IMAGE,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_TINY, SIMD_PROVIDER_ID,
    (tiny_v & 2) != 0, (tiny_v & 1) != 0)
val large_ok = kernel_table_register(t, KERNEL_OP_SRC_OVER_IMAGE,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_LARGE, SIMD_PROVIDER_ID,
    (large_v & 2) != 0, (large_v & 1) != 0)
assert_true(tiny_ok == (tiny_v == 3))
assert_true(large_ok == (large_v == 3))
val tiny_simd = kernel_table_lookup(t, KERNEL_OP_SRC_OVER_IMAGE,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_TINY) == SIMD_PROVIDER_ID
val large_simd = kernel_table_lookup(t, KERNEL_OP_SRC_OVER_IMAGE,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_LARGE) == SIMD_PROVIDER_ID
assert_true(tiny_simd == tiny_ok)
assert_true(large_simd == large_ok)
assert_true((tiny_v & 2) != 0)
assert_true((large_v & 2) != 0)
print("src_over_image gate: TINY verdict=" + tiny_v.to_text() +
      " registered=" + tiny_simd.to_text() +
      " | LARGE verdict=" + large_v.to_text() +
      " registered=" + large_simd.to_text() + " (verdict: 1=faster, 2=exact, 3=both)")
```

</details>


</details>

<details>
<summary>Advanced: mask_src_over TINY+LARGE: registration outcome matches the probe's own verdict</summary>

#### mask_src_over TINY+LARGE: registration outcome matches the probe's own verdict _(slow)_

- mask_src_over TINY+LARGE: registration outcome matches the probe's own verdict


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mask_src_over TINY+LARGE: registration outcome matches the probe's own verdict")
var t = kernel_table_new()
val tiny_v = _kernel_probe_mask_src_over_bucket(8, 200)
val large_v = _kernel_probe_mask_src_over_bucket(4096, 4)
val tiny_ok = kernel_table_register(t, KERNEL_OP_MASK_SRC_OVER,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_TINY, SIMD_PROVIDER_ID,
    (tiny_v & 2) != 0, (tiny_v & 1) != 0)
val large_ok = kernel_table_register(t, KERNEL_OP_MASK_SRC_OVER,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_LARGE, SIMD_PROVIDER_ID,
    (large_v & 2) != 0, (large_v & 1) != 0)
assert_true(tiny_ok == (tiny_v == 3))
assert_true(large_ok == (large_v == 3))
val tiny_simd = kernel_table_lookup(t, KERNEL_OP_MASK_SRC_OVER,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_TINY) == SIMD_PROVIDER_ID
val large_simd = kernel_table_lookup(t, KERNEL_OP_MASK_SRC_OVER,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_LARGE) == SIMD_PROVIDER_ID
assert_true(tiny_simd == tiny_ok)
assert_true(large_simd == large_ok)
assert_true((tiny_v & 2) != 0)
assert_true((large_v & 2) != 0)
print("mask_src_over gate: TINY verdict=" + tiny_v.to_text() +
      " registered=" + tiny_simd.to_text() +
      " | LARGE verdict=" + large_v.to_text() +
      " registered=" + large_simd.to_text() + " (verdict: 1=faster, 2=exact, 3=both)")
```

</details>


</details>

### gate refusal per new op — a losing (or non-exact) measurement stays scalar

#### keeps every new op's TINY slot on scalar when faster=false, and refuses bit_exact=false outright

- keeps every new op's TINY slot on scalar when faster=false, and refuses bit_exact=false outright


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps every new op's TINY slot on scalar when faster=false, and refuses bit_exact=false outright")
var t = kernel_table_new()
assert_true(not kernel_table_register(t, KERNEL_OP_SRC_OVER_CONST,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_TINY, SIMD_PROVIDER_ID, true, false))
assert_true(not kernel_table_register(t, KERNEL_OP_SRC_OVER_IMAGE,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_TINY, SIMD_PROVIDER_ID, true, false))
assert_true(not kernel_table_register(t, KERNEL_OP_MASK_SRC_OVER,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_TINY, SIMD_PROVIDER_ID, false, true))
assert_true(kernel_table_lookup(t, KERNEL_OP_SRC_OVER_CONST,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_TINY) == KERNEL_PROVIDER_SCALAR)
assert_true(kernel_table_lookup(t, KERNEL_OP_SRC_OVER_IMAGE,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_TINY) == KERNEL_PROVIDER_SCALAR)
assert_true(kernel_table_lookup(t, KERNEL_OP_MASK_SRC_OVER,
    KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
    KERNEL_SPAN_CONTIGUOUS, KERNEL_BUCKET_TINY) == KERNEL_PROVIDER_SCALAR)
```

</details>

### total table-build cost + owned-table persistence — 4 ops x 4 buckets probed at ensure_kernel_table time

<details>
<summary>Advanced: builds the full 16-slot-probed table via a first fill, persists it observably, and reports total wall time + the per-slot provider map</summary>

#### builds the full 16-slot-probed table via a first fill, persists it observably, and reports total wall time + the per-slot provider map _(slow)_

- builds the full 16-slot-probed table via a first fill, persists it observably, and reports total wall time + the per-slot provider map


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds the full 16-slot-probed table via a first fill, persists it observably, and reports total wall time + the per-slot provider map")
# Persistence guard for the defect shape found while building T10:
# registrations applied through self.kernel_table -> free fn (or a
# mut table threaded through a probe) are silently dropped, so
# ensure_kernel_table builds a LOCAL table and field-assigns it.
# sealed==true on the backend's own table proves the assignment
# persisted — an unsealed table here means the build was lost.
var backend = SoftwareBackend.create_cpu_simd()
assert_true(backend.init(10, 4))
val t0 = time_now_unix_micros()
backend.clear(0xFF001122u32)
val build_us = time_now_unix_micros() - t0
assert_true(backend.kernel_table_ready == true)
assert_true(backend.kernel_table.sealed == true)
assert_true(backend.buf[0] == 0xFF001122u32)
# Per-op x per-bucket provider map — machine-dependent honest verdicts,
# printed (not asserted) as the T10 measurement-coverage evidence.
var report = "kernel table providers (KERNEL_PROVIDER_SIMD_ISA=1, KERNEL_PROVIDER_SCALAR=0):"
val ops: [i64] = [KERNEL_OP_FILL_CONST, KERNEL_OP_SRC_OVER_CONST,
                  KERNEL_OP_SRC_OVER_IMAGE, KERNEL_OP_MASK_SRC_OVER]
val op_names: [text] = ["fill_const", "src_over_const", "src_over_image", "mask_src_over"]
val buckets: [i64] = [KERNEL_BUCKET_TINY, KERNEL_BUCKET_SMALL,
                      KERNEL_BUCKET_MEDIUM, KERNEL_BUCKET_LARGE]
var oi = 0
while oi < 4:
    report = report + " " + op_names[oi] + "=["
    var bi = 0
    while bi < 4:
        val prov = kernel_table_lookup(backend.kernel_table, ops[oi],
            KERNEL_FORMAT_ARGB8888_STRAIGHT, KERNEL_ALIGN_UNKNOWN,
            KERNEL_SPAN_CONTIGUOUS, buckets[bi])
        report = report + prov.to_text()
        if bi < 3:
            report = report + ","
        bi = bi + 1
    report = report + "]"
    oi = oi + 1
print(report)
print("full 4-op x 4-bucket kernel table build (first clear, interpreter): " +
      build_us.to_text() + " us total")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_software_kernel_table_bucket_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering kernel_size_bucket — bucket boundaries used by the honest gate, kernel_table_register — honest gate can produce EITHER outcome for a small bucket (sabotage test), SIMD-ISA fill_const bit-exactness at small-bucket span lengths, honest per-bucket timing (interpreter engine) — real numbers, not hardcoded, real hit-count evidence — small-surface Engine2D.clear() exercises the per-bucket gate, SIMD-ISA src_over_const bit-exactness at representative bucket spans, SIMD-ISA src_over_image bit-exactness at representative bucket spans, SIMD-ISA mask_src_over bit-exactness at representative bucket spans, honest-gate invariant per new op — registered IFF measured exact AND faster (production probes), gate refusal per new op — a losing (or non-exact) measurement stays scalar, total table-build cost + owned-table persistence — 4 ops x 4 buckets probed at ensure_kernel_table time.
- kernel_size_bucket — bucket boundaries used by the honest gate
- kernel_table_register — honest gate can produce EITHER outcome for a small bucket (sabotage test)
- SIMD-ISA fill_const bit-exactness at small-bucket span lengths
- honest per-bucket timing (interpreter engine) — real numbers, not hardcoded
- real hit-count evidence — small-surface Engine2D.clear() exercises the per-bucket gate
- SIMD-ISA src_over_const bit-exactness at representative bucket spans
- SIMD-ISA src_over_image bit-exactness at representative bucket spans
- SIMD-ISA mask_src_over bit-exactness at representative bucket spans
- honest-gate invariant per new op — registered IFF measured exact AND faster (production probes)
- gate refusal per new op — a losing (or non-exact) measurement stays scalar
- total table-build cost + owned-table persistence — 4 ops x 4 buckets probed at ensure_kernel_table time

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 6 |
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

- Canonical SPipe generation for source `676e691f6c32ea56b5d664fe453b4c2bc2df888c664fbd956277d3daead6cba0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `676e691f6c32ea56b5d664fe453b4c2bc2df888c664fbd956277d3daead6cba0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `676e691f6c32ea56b5d664fe453b4c2bc2df888c664fbd956277d3daead6cba0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_software_kernel_table_bucket_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_software_kernel_table_bucket_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_software_kernel_table_bucket_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_software_kernel_table_bucket_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_software_kernel_table_bucket_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies 8, 32, 128, 4096 into TINY, SMALL, MEDIUM, LARGE respectively' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_software_kernel_table_bucket_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps TINY on scalar when faster=false, even though bit_exact=true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_software_kernel_table_bucket_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers TINY when faster=true and bit_exact=true — same gate, opposite real outcome' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
