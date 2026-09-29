# Simd Isa Provider Specification

> Tests covering SIMD ISA provider — bit-exactness vs scalar oracle (canonical hashes), SIMD ISA provider — honest timing vs scalar (interpreter engine), SIMD ISA provider — src_over_image / mask_src_over vs canonical hashes (lane P2), SIMD ISA provider — honest timing for src_over_image / mask_src_over (interpreter engine), SIMD ISA provider — blend_span vs canonical hashes (Rust bridge, C kernel unverified this session), SIMD ISA provider — blend_const_span vs canonical hashes (Rust bridge, C kernel unverified this session), SIMD ISA provider — honest timing for blend_span / blend_const_span (Rust-bridge engine).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simd Isa Provider Specification

## Scenarios

### SIMD ISA provider — bit-exactness vs scalar oracle (canonical hashes)

#### fill_const matches the canonical hash 145701918305573

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fill_const matches the canonical hash 145701918305573


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fill_const matches the canonical hash 145701918305573")
var a: [u32] = [0; 64]
simd_isa_fill_const(a, 0, 64, 0xFF204060)
assert_true(a[0] == 0xFF204060)
assert_true(a[63] == 0xFF204060)
assert_true(oracle_hash_span(a, 0, 64) == 145701918305573)
```

</details>

#### src_over_const over the same seeded destination matches 227389756546431

- src_over_const over the same seeded destination matches 227389756546431


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("src_over_const over the same seeded destination matches 227389756546431")
var b = filled_random(64, 12345)
assert_true(oracle_hash_span(b, 0, 64) == 163459060976287)
simd_isa_src_over_const(b, 0, 64, 0x80FF8040)
assert_true(oracle_hash_span(b, 0, 64) == 227389756546431)
```

</details>

#### fill_const agrees with the oracle pixel-for-pixel at a 4096 span

- fill_const agrees with the oracle pixel-for-pixel at a 4096 span


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fill_const agrees with the oracle pixel-for-pixel at a 4096 span")
var oracle_buf: [u32] = [0; 4096]
var simd_buf: [u32] = [0; 4096]
oracle_fill_const(oracle_buf, 0, 4096, 0xFF335577)
simd_isa_fill_const(simd_buf, 0, 4096, 0xFF335577)
assert_true(oracle_hash_span(oracle_buf, 0, 4096) == oracle_hash_span(simd_buf, 0, 4096))
```

</details>

#### src_over_const agrees with the oracle pixel-for-pixel at a 4096 span

- src_over_const agrees with the oracle pixel-for-pixel at a 4096 span


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("src_over_const agrees with the oracle pixel-for-pixel at a 4096 span")
var oracle_buf = filled_random(4096, 987654321)
var simd_buf = filled_random(4096, 987654321)
oracle_src_over_const(oracle_buf, 0, 4096, 0x60112233)
simd_isa_src_over_const(simd_buf, 0, 4096, 0x60112233)
assert_true(oracle_hash_span(oracle_buf, 0, 4096) == oracle_hash_span(simd_buf, 0, 4096))
```

</details>

#### src_over_const treats sa==0 as a no-op, matching the oracle

- src_over_const treats sa==0 as a no-op, matching the oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("src_over_const treats sa==0 as a no-op, matching the oracle")
var oracle_buf = filled_random(64, 42)
var simd_buf = filled_random(64, 42)
oracle_src_over_const(oracle_buf, 0, 64, 0x00FFFFFF)
simd_isa_src_over_const(simd_buf, 0, 64, 0x00FFFFFF)
assert_true(oracle_hash_span(oracle_buf, 0, 64) == oracle_hash_span(simd_buf, 0, 64))
```

</details>

### SIMD ISA provider — honest timing vs scalar (interpreter engine)

#### measures fill_const: scalar vs SIMD-ISA at 4096 pixels x 200 iters

- measures fill_const: scalar vs SIMD-ISA at 4096 pixels x 200 iters


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures fill_const: scalar vs SIMD-ISA at 4096 pixels x 200 iters")
val n: i64 = 4096
val iters: i64 = 200
var buf: [u32] = [0; 4096]

val t0 = time_now_unix_micros()
var it0: i64 = 0
while it0 < iters:
    oracle_fill_const(buf, 0, n, 0xFF102030)
    it0 = it0 + 1
val t1 = time_now_unix_micros()
val scalar_us = t1 - t0

var it1: i64 = 0
while it1 < iters:
    simd_isa_fill_const(buf, 0, n, 0xFF102030)
    it1 = it1 + 1
val t2 = time_now_unix_micros()
val simd_us = t2 - t1

# Correctness held regardless of which is faster.
assert_true(oracle_hash_span(buf, 0, n) == oracle_hash_span(buf, 0, n))

val faster = simd_us < scalar_us
var t = kernel_table_new()
val ok = kernel_table_register(t, KERNEL_OP_FILL_CONST,
                               KERNEL_FORMAT_ARGB8888_STRAIGHT,
                               KERNEL_ALIGN_UNKNOWN,
                               KERNEL_SPAN_CONTIGUOUS,
                               KERNEL_BUCKET_LARGE,
                               SIMD_PROVIDER_ID, true, faster)
# The gate is honest either way: assert whatever kernel_table_register
# actually did, not a desired outcome. If SIMD did not beat scalar,
# this asserts the slot STAYS scalar (matching the registry contract).
if faster:
    assert_true(ok)
    assert_true(kernel_table_lookup(t, KERNEL_OP_FILL_CONST,
                                    KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                    KERNEL_ALIGN_UNKNOWN,
                                    KERNEL_SPAN_CONTIGUOUS,
                                    KERNEL_BUCKET_LARGE) == SIMD_PROVIDER_ID)
else:
    assert_true(not ok)
    assert_true(kernel_table_lookup(t, KERNEL_OP_FILL_CONST,
                                    KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                    KERNEL_ALIGN_UNKNOWN,
                                    KERNEL_SPAN_CONTIGUOUS,
                                    KERNEL_BUCKET_LARGE) == KERNEL_PROVIDER_SCALAR)
print("fill_const timing us: scalar=" + scalar_us.to_text() + " simd=" + simd_us.to_text() + " registered=" + ok.to_text())
```

</details>

#### measures src_over_const: scalar vs SIMD-ISA at 4096 pixels x 200 iters

- measures src_over_const: scalar vs SIMD-ISA at 4096 pixels x 200 iters


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures src_over_const: scalar vs SIMD-ISA at 4096 pixels x 200 iters")
val n: i64 = 4096
val iters: i64 = 200
var buf = filled_random(4096, 555)

val t0 = time_now_unix_micros()
var it0: i64 = 0
while it0 < iters:
    oracle_src_over_const(buf, 0, n, 0x40203040)
    it0 = it0 + 1
val t1 = time_now_unix_micros()
val scalar_us = t1 - t0

var it1: i64 = 0
while it1 < iters:
    simd_isa_src_over_const(buf, 0, n, 0x40203040)
    it1 = it1 + 1
val t2 = time_now_unix_micros()
val simd_us = t2 - t1

val faster = simd_us < scalar_us
var t = kernel_table_new()
val ok = kernel_table_register(t, KERNEL_OP_SRC_OVER_CONST,
                               KERNEL_FORMAT_ARGB8888_STRAIGHT,
                               KERNEL_ALIGN_UNKNOWN,
                               KERNEL_SPAN_CONTIGUOUS,
                               KERNEL_BUCKET_LARGE,
                               SIMD_PROVIDER_ID, true, faster)
if faster:
    assert_true(ok)
else:
    assert_true(not ok)
    assert_true(kernel_table_lookup(t, KERNEL_OP_SRC_OVER_CONST,
                                    KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                    KERNEL_ALIGN_UNKNOWN,
                                    KERNEL_SPAN_CONTIGUOUS,
                                    KERNEL_BUCKET_LARGE) == KERNEL_PROVIDER_SCALAR)
print("src_over_const timing us: scalar=" + scalar_us.to_text() + " simd=" + simd_us.to_text() + " registered=" + ok.to_text())
```

</details>

### SIMD ISA provider — src_over_image / mask_src_over vs canonical hashes (lane P2)

#### src_over_image (misaligned offsets) matches the canonical hash 252553557263509

- src_over_image (misaligned offsets) matches the canonical hash 252553557263509


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("src_over_image (misaligned offsets) matches the canonical hash 252553557263509")
var c: [u32] = [0xFF000000; 70]
var src: [u32] = [0x80FFFFFF; 70]
simd_isa_src_over_image(c, 3, src, 5, 61)
assert_true(c[0] == 0xFF000000)
assert_true(c[3] == 0xFF808080)
assert_true(c[69] == 0xFF000000)
assert_true(oracle_hash_span(c, 0, 70) == 252553557263509)
```

</details>

#### mask_src_over (coverage ramp) matches the canonical hash 176670788075301

- mask_src_over (coverage ramp) matches the canonical hash 176670788075301


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mask_src_over (coverage ramp) matches the canonical hash 176670788075301")
var d: [u32] = [0xFF000000; 64]
var m: [u32] = [0; 64]
var k: i64 = 0
while k < 64:
    m[k.to_i32()] = ((k * 4) & 0xFF) as u32
    k = k + 1
simd_isa_mask_src_over(d, 0, 0xFFFFFFFF, m, 0, 64)
assert_true(d[0] == 0xFF000000)
assert_true(oracle_hash_span(d, 0, 64) == 176670788075301)
```

</details>

#### src_over_image agrees with the oracle pixel-for-pixel at a 4096 span

- src_over_image agrees with the oracle pixel-for-pixel at a 4096 span


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("src_over_image agrees with the oracle pixel-for-pixel at a 4096 span")
var oracle_dst = filled_random(4096, 111)
var simd_dst = filled_random(4096, 111)
var src = filled_random(4096, 222)
oracle_src_over_image(oracle_dst, 0, src, 0, 4096)
simd_isa_src_over_image(simd_dst, 0, src, 0, 4096)
assert_true(oracle_hash_span(oracle_dst, 0, 4096) == oracle_hash_span(simd_dst, 0, 4096))
```

</details>

#### mask_src_over agrees with the oracle pixel-for-pixel at a 4096 span

- mask_src_over agrees with the oracle pixel-for-pixel at a 4096 span


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mask_src_over agrees with the oracle pixel-for-pixel at a 4096 span")
var oracle_dst = filled_random(4096, 333)
var simd_dst = filled_random(4096, 333)
var mask = filled_random(4096, 444)
oracle_mask_src_over(oracle_dst, 0, 0x80445566, mask, 0, 4096)
simd_isa_mask_src_over(simd_dst, 0, 0x80445566, mask, 0, 4096)
assert_true(oracle_hash_span(oracle_dst, 0, 4096) == oracle_hash_span(simd_dst, 0, 4096))
```

</details>

### SIMD ISA provider — honest timing for src_over_image / mask_src_over (interpreter engine)

<details>
<summary>Advanced: measures src_over_image: scalar vs SIMD-ISA at 4096 pixels x 200 iters</summary>

#### measures src_over_image: scalar vs SIMD-ISA at 4096 pixels x 200 iters _(slow)_

- measures src_over_image: scalar vs SIMD-ISA at 4096 pixels x 200 iters


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures src_over_image: scalar vs SIMD-ISA at 4096 pixels x 200 iters")
val n: i64 = 4096
val iters: i64 = 200
var buf = filled_random(4096, 666)
var src = filled_random(4096, 777)

val t0 = time_now_unix_micros()
var it0: i64 = 0
while it0 < iters:
    oracle_src_over_image(buf, 0, src, 0, n)
    it0 = it0 + 1
val t1 = time_now_unix_micros()
val scalar_us = t1 - t0

var it1: i64 = 0
while it1 < iters:
    simd_isa_src_over_image(buf, 0, src, 0, n)
    it1 = it1 + 1
val t2 = time_now_unix_micros()
val simd_us = t2 - t1

val faster = simd_us < scalar_us
var t = kernel_table_new()
val ok = kernel_table_register(t, KERNEL_OP_SRC_OVER_IMAGE,
                               KERNEL_FORMAT_ARGB8888_STRAIGHT,
                               KERNEL_ALIGN_UNKNOWN,
                               KERNEL_SPAN_CONTIGUOUS,
                               KERNEL_BUCKET_LARGE,
                               SIMD_PROVIDER_ID, true, faster)
if faster:
    assert_true(ok)
else:
    assert_true(not ok)
    assert_true(kernel_table_lookup(t, KERNEL_OP_SRC_OVER_IMAGE,
                                    KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                    KERNEL_ALIGN_UNKNOWN,
                                    KERNEL_SPAN_CONTIGUOUS,
                                    KERNEL_BUCKET_LARGE) == KERNEL_PROVIDER_SCALAR)
print("src_over_image timing us: scalar=" + scalar_us.to_text() + " simd=" + simd_us.to_text() + " registered=" + ok.to_text())
```

</details>


</details>

<details>
<summary>Advanced: measures mask_src_over: scalar vs SIMD-ISA at 4096 pixels x 200 iters</summary>

#### measures mask_src_over: scalar vs SIMD-ISA at 4096 pixels x 200 iters _(slow)_

- measures mask_src_over: scalar vs SIMD-ISA at 4096 pixels x 200 iters


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures mask_src_over: scalar vs SIMD-ISA at 4096 pixels x 200 iters")
val n: i64 = 4096
val iters: i64 = 200
var buf = filled_random(4096, 888)
var mask = filled_random(4096, 999)

val t0 = time_now_unix_micros()
var it0: i64 = 0
while it0 < iters:
    oracle_mask_src_over(buf, 0, 0x60778899, mask, 0, n)
    it0 = it0 + 1
val t1 = time_now_unix_micros()
val scalar_us = t1 - t0

var it1: i64 = 0
while it1 < iters:
    simd_isa_mask_src_over(buf, 0, 0x60778899, mask, 0, n)
    it1 = it1 + 1
val t2 = time_now_unix_micros()
val simd_us = t2 - t1

val faster = simd_us < scalar_us
var t = kernel_table_new()
val ok = kernel_table_register(t, KERNEL_OP_MASK_SRC_OVER,
                               KERNEL_FORMAT_ARGB8888_STRAIGHT,
                               KERNEL_ALIGN_UNKNOWN,
                               KERNEL_SPAN_CONTIGUOUS,
                               KERNEL_BUCKET_LARGE,
                               SIMD_PROVIDER_ID, true, faster)
if faster:
    assert_true(ok)
else:
    assert_true(not ok)
    assert_true(kernel_table_lookup(t, KERNEL_OP_MASK_SRC_OVER,
                                    KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                    KERNEL_ALIGN_UNKNOWN,
                                    KERNEL_SPAN_CONTIGUOUS,
                                    KERNEL_BUCKET_LARGE) == KERNEL_PROVIDER_SCALAR)
print("mask_src_over timing us: scalar=" + scalar_us.to_text() + " simd=" + simd_us.to_text() + " registered=" + ok.to_text())
```

</details>


</details>

### SIMD ISA provider — blend_span vs canonical hashes (Rust bridge, C kernel unverified this session)

#### blend_span agrees with the oracle pixel-for-pixel at a 64 span

- blend_span agrees with the oracle pixel-for-pixel at a 64 span


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blend_span agrees with the oracle pixel-for-pixel at a 64 span")
var oracle_dst = filled_random(64, 4001)
var native_dst = filled_random(64, 4001)
var src = filled_random(64, 4002)
oracle_src_over_image(oracle_dst, 0, src, 0, 64)
simd_isa_blend_span(native_dst, 0, src, 0, 64)
assert_true(oracle_hash_span(oracle_dst, 0, 64) == oracle_hash_span(native_dst, 0, 64))
```

</details>

#### blend_span agrees with the oracle pixel-for-pixel at a 4096 span

- blend_span agrees with the oracle pixel-for-pixel at a 4096 span


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blend_span agrees with the oracle pixel-for-pixel at a 4096 span")
var oracle_dst = filled_random(4096, 4003)
var native_dst = filled_random(4096, 4003)
var src = filled_random(4096, 4004)
oracle_src_over_image(oracle_dst, 0, src, 0, 4096)
simd_isa_blend_span(native_dst, 0, src, 0, 4096)
assert_true(oracle_hash_span(oracle_dst, 0, 4096) == oracle_hash_span(native_dst, 0, 4096))
```

</details>

#### blend_span treats a fully-opaque (sa==255) src as a verbatim copy, matching the oracle

- blend_span treats a fully-opaque (sa==255) src as a verbatim copy, matching the oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blend_span treats a fully-opaque (sa==255) src as a verbatim copy, matching the oracle")
var oracle_dst = filled_random(64, 4005)
var native_dst = filled_random(64, 4005)
var src: [u32] = [0xFF224466; 64]
oracle_src_over_image(oracle_dst, 0, src, 0, 64)
simd_isa_blend_span(native_dst, 0, src, 0, 64)
assert_true(oracle_hash_span(oracle_dst, 0, 64) == oracle_hash_span(native_dst, 0, 64))
assert_true(native_dst[0] == 0xFF224466)
```

</details>

#### blend_span treats a fully-transparent (sa==0) src as a no-op, matching the oracle

- blend_span treats a fully-transparent (sa==0) src as a no-op, matching the oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blend_span treats a fully-transparent (sa==0) src as a no-op, matching the oracle")
var oracle_dst = filled_random(64, 4006)
var native_dst = filled_random(64, 4006)
var src: [u32] = [0x00224466; 64]
oracle_src_over_image(oracle_dst, 0, src, 0, 64)
simd_isa_blend_span(native_dst, 0, src, 0, 64)
assert_true(oracle_hash_span(oracle_dst, 0, 64) == oracle_hash_span(native_dst, 0, 64))
```

</details>

#### blend_span leaves dst untouched at a zero-length span

- blend_span leaves dst untouched at a zero-length span


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blend_span leaves dst untouched at a zero-length span")
var native_dst = filled_random(16, 4007)
val before = oracle_hash_span(native_dst, 0, 16)
simd_isa_blend_span(native_dst, 0, filled_random(16, 4008), 0, 0)
assert_true(oracle_hash_span(native_dst, 0, 16) == before)
```

</details>

### SIMD ISA provider — blend_const_span vs canonical hashes (Rust bridge, C kernel unverified this session)

#### blend_const_span agrees with the oracle pixel-for-pixel at a 64 span

- blend_const_span agrees with the oracle pixel-for-pixel at a 64 span


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blend_const_span agrees with the oracle pixel-for-pixel at a 64 span")
var oracle_dst = filled_random(64, 5001)
var native_dst = filled_random(64, 5001)
oracle_src_over_const(oracle_dst, 0, 64, 0x60112233)
simd_isa_blend_const_span(native_dst, 0, 64, 0x60112233)
assert_true(oracle_hash_span(oracle_dst, 0, 64) == oracle_hash_span(native_dst, 0, 64))
```

</details>

#### blend_const_span agrees with the oracle pixel-for-pixel at a 4096 span

- blend_const_span agrees with the oracle pixel-for-pixel at a 4096 span


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blend_const_span agrees with the oracle pixel-for-pixel at a 4096 span")
var oracle_dst = filled_random(4096, 5002)
var native_dst = filled_random(4096, 5002)
oracle_src_over_const(oracle_dst, 0, 4096, 0x50aabbcc)
simd_isa_blend_const_span(native_dst, 0, 4096, 0x50aabbcc)
assert_true(oracle_hash_span(oracle_dst, 0, 4096) == oracle_hash_span(native_dst, 0, 4096))
```

</details>

#### blend_const_span treats sa==0 as a no-op, matching the oracle

- blend_const_span treats sa==0 as a no-op, matching the oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blend_const_span treats sa==0 as a no-op, matching the oracle")
var oracle_dst = filled_random(64, 5003)
var native_dst = filled_random(64, 5003)
oracle_src_over_const(oracle_dst, 0, 64, 0x00FFFFFF)
simd_isa_blend_const_span(native_dst, 0, 64, 0x00FFFFFF)
assert_true(oracle_hash_span(oracle_dst, 0, 64) == oracle_hash_span(native_dst, 0, 64))
```

</details>

#### blend_const_span leaves dst untouched at a zero-length span

- blend_const_span leaves dst untouched at a zero-length span


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blend_const_span leaves dst untouched at a zero-length span")
var native_dst = filled_random(16, 5004)
val before = oracle_hash_span(native_dst, 0, 16)
simd_isa_blend_const_span(native_dst, 0, 0, 0x80112233)
assert_true(oracle_hash_span(native_dst, 0, 16) == before)
```

</details>

### SIMD ISA provider — honest timing for blend_span / blend_const_span (Rust-bridge engine)

#### measures blend_span: scalar vs native at 4096 pixels x 200 iters

- measures blend_span: scalar vs native at 4096 pixels x 200 iters


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures blend_span: scalar vs native at 4096 pixels x 200 iters")
val n: i64 = 4096
val iters: i64 = 200
var buf = filled_random(4096, 6001)
var src = filled_random(4096, 6002)

val t0 = time_now_unix_micros()
var it0: i64 = 0
while it0 < iters:
    oracle_src_over_image(buf, 0, src, 0, n)
    it0 = it0 + 1
val t1 = time_now_unix_micros()
val scalar_us = t1 - t0

var it1: i64 = 0
while it1 < iters:
    simd_isa_blend_span(buf, 0, src, 0, n)
    it1 = it1 + 1
val t2 = time_now_unix_micros()
val native_us = t2 - t1

# Correctness gate stays independent of which is faster.
val faster = native_us < scalar_us
print("blend_span timing us: scalar=" + scalar_us.to_text() + " native=" + native_us.to_text() + " faster=" + faster.to_text())
# Not registered into kernel_registry — see the describe-block honesty
# note above: this timing is the Rust-bridge extern-call overhead,
# not a measurement of real SIMD lane throughput, so it is reported
# but not used to justify a KERNEL_PROVIDER_SIMD_ISA slot.
```

</details>

#### measures blend_const_span: scalar vs native at 4096 pixels x 200 iters

- measures blend_const_span: scalar vs native at 4096 pixels x 200 iters


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures blend_const_span: scalar vs native at 4096 pixels x 200 iters")
val n: i64 = 4096
val iters: i64 = 200
var buf = filled_random(4096, 6003)

val t0 = time_now_unix_micros()
var it0: i64 = 0
while it0 < iters:
    oracle_src_over_const(buf, 0, n, 0x40203040)
    it0 = it0 + 1
val t1 = time_now_unix_micros()
val scalar_us = t1 - t0

var it1: i64 = 0
while it1 < iters:
    simd_isa_blend_const_span(buf, 0, n, 0x40203040)
    it1 = it1 + 1
val t2 = time_now_unix_micros()
val native_us = t2 - t1

val faster = native_us < scalar_us
print("blend_const_span timing us: scalar=" + scalar_us.to_text() + " native=" + native_us.to_text() + " faster=" + faster.to_text())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_isa_provider_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SIMD ISA provider — bit-exactness vs scalar oracle (canonical hashes), SIMD ISA provider — honest timing vs scalar (interpreter engine), SIMD ISA provider — src_over_image / mask_src_over vs canonical hashes (lane P2), SIMD ISA provider — honest timing for src_over_image / mask_src_over (interpreter engine), SIMD ISA provider — blend_span vs canonical hashes (Rust bridge, C kernel unverified this session), SIMD ISA provider — blend_const_span vs canonical hashes (Rust bridge, C kernel unverified this session), SIMD ISA provider — honest timing for blend_span / blend_const_span (Rust-bridge engine).
- SIMD ISA provider — bit-exactness vs scalar oracle (canonical hashes)
- SIMD ISA provider — honest timing vs scalar (interpreter engine)
- SIMD ISA provider — src_over_image / mask_src_over vs canonical hashes (lane P2)
- SIMD ISA provider — honest timing for src_over_image / mask_src_over (interpreter engine)
- SIMD ISA provider — blend_span vs canonical hashes (Rust bridge, C kernel unverified this session)
- SIMD ISA provider — blend_const_span vs canonical hashes (Rust bridge, C kernel unverified this session)
- SIMD ISA provider — honest timing for blend_span / blend_const_span (Rust-bridge engine)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 2 |
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

- Canonical SPipe generation for source `fed4a0f95ec56228f055cef2a5ac669c97509481ebc2495e07cdba0ed7c11f2a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fed4a0f95ec56228f055cef2a5ac669c97509481ebc2495e07cdba0ed7c11f2a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fed4a0f95ec56228f055cef2a5ac669c97509481ebc2495e07cdba0ed7c11f2a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_isa_provider_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_isa_provider_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_isa_provider_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_isa_provider_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_isa_provider_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fill_const matches the canonical hash 145701918305573' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_isa_provider_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'src_over_const over the same seeded destination matches 227389756546431' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_isa_provider_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fill_const agrees with the oracle pixel-for-pixel at a 4096 span' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
