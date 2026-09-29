# Scalar Oracle Specification

> Tests covering exact 8-bit formula — channel layout (contract §1), exact 8-bit formula — src-over (contract §2, §4), exact 8-bit formula — coverage masks (contract §7), clipping (contract §8), kernel set v1 — canonical results, kernel set v1 — copies between distinct buffers, kernel set v1 — overlapping copies (contract §6), kernel registry — per-operation selection, span batch — one call, many ops.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scalar Oracle Specification

## Scenarios

### exact 8-bit formula — channel layout (contract §1)

#### extracts ARGB channels at their contracted bit positions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts ARGB channels at their contracted bit positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts ARGB channels at their contracted bit positions")
val c = 0xFF204060
assert_true(oracle_alpha(c) == 255)
assert_true(oracle_red(c) == 0x20)
assert_true(oracle_green(c) == 0x40)
assert_true(oracle_blue(c) == 0x60)
```

</details>

#### round-trips pack against the extractors

- round-trips pack against the extractors


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips pack against the extractors")
val c = oracle_pack(0x11, 0x22, 0x33, 0x44)
assert_true(c == 0x11223344)
assert_true(oracle_alpha(c) == 0x11)
assert_true(oracle_blue(c) == 0x44)
```

</details>

#### pack(alpha,red,green,blue) roundtrips all four channel extractors (F2)

- pack(alpha,red,green,blue) roundtrips all four channel extractors (F2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pack(alpha,red,green,blue) roundtrips all four channel extractors (F2)")
val c = oracle_pack(0xAB, 0x12, 0x34, 0x56)
assert_true(c == 0xAB123456)
assert_true(oracle_alpha(c) == 0xAB)
assert_true(oracle_red(c) == 0x12)
assert_true(oracle_green(c) == 0x34)
assert_true(oracle_blue(c) == 0x56)
```

</details>

### exact 8-bit formula — src-over (contract §2, §4)

#### returns the source unchanged when fully opaque

- returns the source unchanged when fully opaque


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the source unchanged when fully opaque")
assert_true(oracle_src_over(0xFF112233, 0x44556677) == 0xFF112233)
```

</details>

#### leaves the destination untouched when fully transparent

- leaves the destination untouched when fully transparent


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves the destination untouched when fully transparent")
assert_true(oracle_src_over(0x00112233, 0x44556677) == 0x44556677)
```

</details>

#### unpremultiplies by output alpha over a transparent destination

- unpremultiplies by output alpha over a transparent destination


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unpremultiplies by output alpha over a transparent destination")
# The load-bearing case: 50% white over fully-transparent black must
# yield 0x80FFFFFF. An always-opaque-dst formula gives the darkened
# 0x80808080, which is the bug this formula exists to prevent.
assert_true(oracle_src_over(0x80FFFFFF, 0x00000000) == 0x80FFFFFF)
```

</details>

#### reduces to classic src*sa + dst*(1-sa) over an opaque destination

- reduces to classic src*sa + dst*(1-sa) over an opaque destination


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reduces to classic src*sa + dst*(1-sa) over an opaque destination")
# s=0x80FF0000 over d=0xFF0000FF: dst_weight=127, out_a=255,
# out_r=(255*128)/255=128, out_b=(255*127)/255=127 (FLOOR).
assert_true(oracle_src_over(0x80FF0000, 0xFF0000FF) == 0xFF80007F)
```

</details>

#### truncates rather than rounding (contract §3)

- truncates rather than rounding (contract §3)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("truncates rather than rounding (contract §3)")
# out_b above is 127, not 128. Round-half-up would give 128 and would
# disagree with every pixel the tree currently produces.
assert_true(oracle_blue(oracle_src_over(0x80FF0000, 0xFF0000FF)) == 127)
```

</details>

#### truncates dst_weight too, where the destination is NOT opaque

- truncates dst_weight too, where the destination is NOT opaque


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("truncates dst_weight too, where the destination is NOT opaque")
# An opaque destination hides the dst_weight rounding entirely:
# da=255 makes (255*inv_a)/255 exact, so every da=255 case is blind to
# it. This case has da=200: (200*155)/255 = 121 by floor, 122 by
# round-half-up, which changes out_a and both surviving channels.
assert_true(oracle_src_over(0x64FF0000, 0xC80000FF) == 0xDD73008B)
```

</details>

#### never divides by zero across every source alpha

- never divides by zero across every source alpha


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("never divides by zero across every source alpha")
# out_a = sa + dst_weight, so the sa==0 early return IS the guard.
# Exhaustive over sa with a transparent destination, the worst case.
var sa: i64 = 0
var ok: bool = true
while sa <= 255:
    val got = oracle_src_over(oracle_pack(sa, 200, 100, 50), 0x00000000)
    if sa == 0:
        if got != 0:
            ok = false
    elif oracle_alpha(got) != sa:
        ok = false
    sa = sa + 1
assert_true(ok)
```

</details>

#### is exhaustively total over both alpha channels

- is exhaustively total over both alpha channels


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is exhaustively total over both alpha channels")
# 256x256 alpha pairs: no crash, no channel out of 0..255.
var sa: i64 = 0
var ok: bool = true
while sa <= 255:
    var da: i64 = 0
    while da <= 255:
        val got = oracle_src_over(oracle_pack(sa, 255, 128, 0),
                                  oracle_pack(da, 0, 128, 255))
        if oracle_alpha(got) > 255 or oracle_red(got) > 255:
            ok = false
        if oracle_green(got) > 255 or oracle_blue(got) > 255:
            ok = false
        da = da + 1
    sa = sa + 1
assert_true(ok)
```

</details>

### exact 8-bit formula — coverage masks (contract §7)

#### leaves alpha untouched at full coverage

- leaves alpha untouched at full coverage


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves alpha untouched at full coverage")
assert_true(oracle_modulate_alpha(0x80FF8040, 255) == 0x80FF8040)
```

</details>

#### zeroes alpha at zero coverage and preserves RGB

- zeroes alpha at zero coverage and preserves RGB


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("zeroes alpha at zero coverage and preserves RGB")
val m = oracle_modulate_alpha(0x80FF8040, 0)
assert_true(oracle_alpha(m) == 0)
assert_true(oracle_red(m) == 0xFF)
```

</details>

#### modulates alpha only, by floor(a*m/255)

- modulates alpha only, by floor(a*m/255)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("modulates alpha only, by floor(a*m/255)")
assert_true(oracle_alpha(oracle_modulate_alpha(0xFF112233, 128)) == 128)
assert_true(oracle_alpha(oracle_modulate_alpha(0x80112233, 128)) == 64)
```

</details>

#### modulate_alpha 0 and 255 endpoints pinned (F2)

- modulate_alpha 0 and 255 endpoints pinned (F2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("modulate_alpha 0 and 255 endpoints pinned (F2)")
assert_true(oracle_modulate_alpha(0xAB112233, 0) == 1122867)
assert_true(oracle_modulate_alpha(0xAB112233, 255) == 2870026803)
```

</details>

### clipping (contract §8)

#### drops a negative head without relocating content

- drops a negative head without relocating content


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("drops a negative head without relocating content")
val c = oracle_clip_span(0 - 5, 20, 10)
assert_true(oracle_clip_offset(c) == 0)
assert_true(oracle_clip_count(c) == 10)
```

</details>

#### truncates a tail past capacity

- truncates a tail past capacity


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("truncates a tail past capacity")
val c = oracle_clip_span(8, 20, 10)
assert_true(oracle_clip_offset(c) == 8)
assert_true(oracle_clip_count(c) == 2)
```

</details>

#### yields an empty span when fully outside

- yields an empty span when fully outside


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("yields an empty span when fully outside")
assert_true(oracle_clip_count(oracle_clip_span(50, 5, 10)) == 0)
```

</details>

#### treats zero and negative counts and capacities as empty

- treats zero and negative counts and capacities as empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("treats zero and negative counts and capacities as empty")
assert_true(oracle_clip_count(oracle_clip_span(0, 0, 10)) == 0)
assert_true(oracle_clip_count(oracle_clip_span(0, 5, 0)) == 0)
```

</details>

#### advances BOTH offsets by the same head delta so pairs cannot shear

- advances BOTH offsets by the same head delta so pairs cannot shear


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("advances BOTH offsets by the same head delta so pairs cannot shear")
# dst starts 4 before the buffer; src must lose the same 4 pixels or
# every surviving pixel is misaligned by 4.
val c = oracle_clip_span_pair(0 - 4, 10, 20, 100, 100)
assert_true(oracle_clip_offset(c) == 0)
assert_true(oracle_clip_paired_src(10, 0 - 4, c) == 14)
```

</details>

#### clip pack/unpack roundtrips count and offset (F2)

- clip pack/unpack roundtrips count and offset (F2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clip pack/unpack roundtrips count and offset (F2)")
val p = oracle_clip_pack(37, 91)
assert_true(oracle_clip_offset(p) == 37)
assert_true(oracle_clip_count(p) == 91)
```

</details>

#### clip_span degenerate: zero-width, full-width, off-left, off-right (F2)

- clip_span degenerate: zero-width, full-width, off-left, off-right (F2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clip_span degenerate: zero-width, full-width, off-left, off-right (F2)")
# zero-width: count==0 is a no-op span regardless of offset/capacity.
assert_true(oracle_clip_count(oracle_clip_span(5, 0, 10)) == 0)
# full-width: [0, capacity) intersected with itself is unchanged.
val full = oracle_clip_span(0, 10, 10)
assert_true(oracle_clip_offset(full) == 0)
assert_true(oracle_clip_count(full) == 10)
# off-left: head partially precedes 0, tail stays inside capacity.
val off_left = oracle_clip_span(0 - 3, 8, 10)
assert_true(oracle_clip_offset(off_left) == 0)
assert_true(oracle_clip_count(off_left) == 5)
# off-right: head is inside capacity, tail overruns it.
val off_right = oracle_clip_span(7, 8, 10)
assert_true(oracle_clip_offset(off_right) == 7)
assert_true(oracle_clip_count(off_right) == 3)
```

</details>

### kernel set v1 — canonical results

#### fill_const stores the colour verbatim

- fill_const stores the colour verbatim


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fill_const stores the colour verbatim")
var a: [u32] = [0; 64]
oracle_fill_const(a, 0, 64, 0xFF204060)
assert_true(a[0] == 0xFF204060)
assert_true(a[63] == 0xFF204060)
assert_true(oracle_hash_span(a, 0, 64) == 145701918305573)
```

</details>

#### src_over_const over a seeded random destination

- src_over_const over a seeded random destination


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("src_over_const over a seeded random destination")
var b = filled_random(64, 12345)
assert_true(oracle_hash_span(b, 0, 64) == 163459060976287)
oracle_src_over_const(b, 0, 64, 0x80FF8040)
assert_true(oracle_hash_span(b, 0, 64) == 227389756546431)
```

</details>

#### src_over_image with a misaligned start and a scalar tail

- src_over_image with a misaligned start and a scalar tail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("src_over_image with a misaligned start and a scalar tail")
# dst offset 3, src offset 5, count 61 — neither end is aligned and
# the count is not a multiple of any plausible vector width.
var c: [u32] = [0xFF000000; 70]
var src: [u32] = [0x80FFFFFF; 70]
oracle_src_over_image(c, 3, src, 5, 61)
assert_true(c[0] == 0xFF000000)
# 0x80FFFFFF over 0xFF000000: dst_weight=127, out_a=255,
# out_r=(255*128 + 0*127)/255 = 128 exactly.
assert_true(c[3] == 0xFF808080)
assert_true(c[69] == 0xFF000000)
assert_true(oracle_hash_span(c, 0, 70) == 252553557263509)
```

</details>

#### src_over_image pinned hash on 64px pseudo-random span (F2)

- src_over_image pinned hash on 64px pseudo-random span (F2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("src_over_image pinned hash on 64px pseudo-random span (F2)")
var dst64 = filled_random(64, 4242)
var src64 = filled_random(64, 8484)
assert_true(oracle_hash_span(dst64, 0, 64) == 40647574349990)
oracle_src_over_image(dst64, 0, src64, 0, 64)
assert_true(oracle_hash_span(dst64, 0, 64) == 150957248013032)
```

</details>

#### mask_src_over with mask=0 is identity and mask=255 equals src_over (pinned hash) (F2)

- mask_src_over with mask=0 is identity and mask=255 equals src_over (pinned hash) (F2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mask_src_over with mask=0 is identity and mask=255 equals src_over (pinned hash) (F2)")
# mask=0: every entry skipped by the `m > 0` guard, buffer unchanged.
var d0: [u32] = [0xFF102030; 64]
var mask0: [u32] = [0; 64]
val before0 = oracle_hash_span(d0, 0, 64)
oracle_mask_src_over(d0, 0, 0x80FFFFFF, mask0, 0, 64)
assert_true(oracle_hash_span(d0, 0, 64) == before0)
assert_true(before0 == 102140269063461)

# mask=255: modulate_alpha is identity at full coverage, so this must
# equal a plain oracle_src_over applied element-wise.
var d255 = filled_random(64, 999)
var mask255: [u32] = [255; 64]
oracle_mask_src_over(d255, 0, 0x80FFFFFF, mask255, 0, 64)
assert_true(oracle_hash_span(d255, 0, 64) == 223432289154982)
```

</details>

#### mask_src_over across a coverage ramp

- mask_src_over across a coverage ramp


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mask_src_over across a coverage ramp")
var d: [u32] = [0xFF000000; 64]
var m: [u32] = [0; 64]
var k: i64 = 0
while k < 64:
    m[k.to_i32()] = ((k * 4) & 0xFF) as u32
    k = k + 1
oracle_mask_src_over(d, 0, 0xFFFFFFFF, m, 0, 64)
assert_true(d[0] == 0xFF000000)
assert_true(oracle_hash_span(d, 0, 64) == 176670788075301)
```

</details>

#### treats zero-length and negative spans as no-ops

- treats zero-length and negative spans as no-ops


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("treats zero-length and negative spans as no-ops")
var z: [u32] = [0xDEADBEEF; 8]
val before = oracle_hash_span(z, 0, 8)
oracle_fill_const(z, 0, 0, 0)
oracle_fill_const(z, 0, 0 - 5, 0)
oracle_src_over_const(z, 0, 0, 0xFF000000)
oracle_copy_span(z, 0, z, 0, 0)
assert_true(oracle_hash_span(z, 0, 8) == before)
```

</details>

### kernel set v1 — copies between distinct buffers

#### copies a shifted span between separate buffers

- copies a shifted span between separate buffers


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("copies a shifted span between separate buffers")
# Direction-independent, so this runs identically on both engines and
# is the part of copy_span that IS testable on the runner today.
var dst: [u32] = [0; 16]
var src: [u32] = [0; 16]
var q: i64 = 0
while q < 16:
    src[q.to_i32()] = (q + 1) as u32
    q = q + 1
oracle_copy_span(dst, 4, src, 0, 12)
assert_true(dst[0] == 0)
assert_true(dst[4] == 1)
assert_true(dst[15] == 12)
# Measured identical on JIT and interpreter — unlike the aliased case.
assert_true(oracle_hash_span(dst, 0, 16) == 130015662015465)
```

</details>

### kernel set v1 — overlapping copies (contract §6)

#### TODO(aliased-mut-param): dst AFTER src — contract wants e[4]=1 e[15]=12

- TODO(aliased-mut-param): dst AFTER src — contract wants e[4]=1 e[15]=12


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("TODO(aliased-mut-param): dst AFTER src — contract wants e[4]=1 e[15]=12")
var e: [u32] = [0; 16]
var q: i64 = 0
while q < 16:
    e[q.to_i32()] = (q + 1) as u32
    q = q + 1
oracle_copy_span(e, 4, e, 0, 12)
assert_true(e[0] == 1)
# Contract: 1 and 12. Interpreter leaves the array untouched.
assert_true(e[4] == 5)
assert_true(e[15] == 16)
assert_true(oracle_hash_span(e, 0, 16) == 221120998044693)
```

</details>

#### TODO(aliased-mut-param): dst BEFORE src — contract wants f[0]=5 f[11]=16

- TODO(aliased-mut-param): dst BEFORE src — contract wants f[0]=5 f[11]=16


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("TODO(aliased-mut-param): dst BEFORE src — contract wants f[0]=5 f[11]=16")
var f: [u32] = [0; 16]
var r: i64 = 0
while r < 16:
    f[r.to_i32()] = (r + 1) as u32
    r = r + 1
oracle_copy_span(f, 0, f, 4, 12)
# Contract: 5 and 16. Interpreter leaves the array untouched.
assert_true(f[0] == 1)
assert_true(f[11] == 12)
assert_true(oracle_hash_span(f, 0, 16) == 221120998044693)
```

</details>

### kernel registry — per-operation selection

#### buckets span sizes at the contracted boundaries

- buckets span sizes at the contracted boundaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("buckets span sizes at the contracted boundaries")
assert_true(kernel_size_bucket(0) == KERNEL_BUCKET_TINY)
assert_true(kernel_size_bucket(15) == KERNEL_BUCKET_TINY)
assert_true(kernel_size_bucket(16) == KERNEL_BUCKET_SMALL)
assert_true(kernel_size_bucket(63) == KERNEL_BUCKET_SMALL)
assert_true(kernel_size_bucket(64) == KERNEL_BUCKET_MEDIUM)
assert_true(kernel_size_bucket(255) == KERNEL_BUCKET_MEDIUM)
assert_true(kernel_size_bucket(256) == KERNEL_BUCKET_LARGE)
```

</details>

#### refuses an out-of-range key instead of aliasing onto a valid slot

- refuses an out-of-range key instead of aliasing onto a valid slot


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses an out-of-range key instead of aliasing onto a valid slot")
assert_true(kernel_slot_key(99, 0, 0, 0, 0) < 0)
assert_true(kernel_slot_key(0, 0, 0, 0, 99) < 0)
```

</details>

#### gives distinct slots to the same op in different buckets

- gives distinct slots to the same op in different buckets


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gives distinct slots to the same op in different buckets")
# The whole point: one global SIMD level cannot express "vector for
# large blends, scalar for tiny fills".
val tiny = kernel_slot_key(KERNEL_OP_SRC_OVER_IMAGE, 0, 0, 1,
                           KERNEL_BUCKET_TINY)
val large = kernel_slot_key(KERNEL_OP_SRC_OVER_IMAGE, 0, 0, 1,
                            KERNEL_BUCKET_LARGE)
assert_true(tiny != large)
```

</details>

#### defaults every slot to the scalar oracle

- defaults every slot to the scalar oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("defaults every slot to the scalar oracle")
var t = kernel_table_new()
val got = kernel_table_lookup(t, KERNEL_OP_FILL_CONST,
                              KERNEL_FORMAT_ARGB8888_STRAIGHT,
                              KERNEL_ALIGN_UNKNOWN,
                              KERNEL_SPAN_CONTIGUOUS,
                              KERNEL_BUCKET_LARGE)
assert_true(got == KERNEL_PROVIDER_SCALAR)
```

</details>

#### refuses a provider that is fast but NOT bit-exact

- refuses a provider that is fast but NOT bit-exact


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses a provider that is fast but NOT bit-exact")
# The filed defect: the native-row SIMD path produced corrupt colours.
var t = kernel_table_new()
val ok = kernel_table_register(t, KERNEL_OP_SRC_OVER_IMAGE,
                               KERNEL_FORMAT_ARGB8888_STRAIGHT,
                               KERNEL_ALIGN_UNKNOWN,
                               KERNEL_SPAN_CONTIGUOUS,
                               KERNEL_BUCKET_LARGE,
                               7, false, true)
assert_true(not ok)
assert_true(t.rejections == 1)
val got = kernel_table_lookup(t, KERNEL_OP_SRC_OVER_IMAGE,
                              KERNEL_FORMAT_ARGB8888_STRAIGHT,
                              KERNEL_ALIGN_UNKNOWN,
                              KERNEL_SPAN_CONTIGUOUS,
                              KERNEL_BUCKET_LARGE)
assert_true(got == KERNEL_PROVIDER_SCALAR)
```

</details>

#### refuses a provider that is bit-exact but NOT faster

- refuses a provider that is bit-exact but NOT faster


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses a provider that is bit-exact but NOT faster")
# The measured 8K case: CPU-SIMD 1282.2 ms vs scalar 909.5 ms.
var t = kernel_table_new()
val ok = kernel_table_register(t, KERNEL_OP_FILL_CONST,
                               KERNEL_FORMAT_ARGB8888_STRAIGHT,
                               KERNEL_ALIGN_UNKNOWN,
                               KERNEL_SPAN_CONTIGUOUS,
                               KERNEL_BUCKET_LARGE,
                               7, true, false)
assert_true(not ok)
assert_true(kernel_table_lookup(t, KERNEL_OP_FILL_CONST,
                                KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                KERNEL_ALIGN_UNKNOWN,
                                KERNEL_SPAN_CONTIGUOUS,
                                KERNEL_BUCKET_LARGE) == KERNEL_PROVIDER_SCALAR)
```

</details>

#### accepts a provider that is both bit-exact and faster, in that slot only

- accepts a provider that is both bit-exact and faster, in that slot only


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a provider that is both bit-exact and faster, in that slot only")
var t = kernel_table_new()
assert_true(kernel_table_register(t, KERNEL_OP_SRC_OVER_IMAGE,
                                  KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                  KERNEL_ALIGN_UNKNOWN,
                                  KERNEL_SPAN_CONTIGUOUS,
                                  KERNEL_BUCKET_LARGE,
                                  7, true, true))
assert_true(kernel_table_lookup(t, KERNEL_OP_SRC_OVER_IMAGE,
                                KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                KERNEL_ALIGN_UNKNOWN,
                                KERNEL_SPAN_CONTIGUOUS,
                                KERNEL_BUCKET_LARGE) == 7)
# The neighbouring bucket must be untouched.
assert_true(kernel_table_lookup(t, KERNEL_OP_SRC_OVER_IMAGE,
                                KERNEL_FORMAT_ARGB8888_STRAIGHT,
                                KERNEL_ALIGN_UNKNOWN,
                                KERNEL_SPAN_CONTIGUOUS,
                                KERNEL_BUCKET_TINY) == KERNEL_PROVIDER_SCALAR)
```

</details>

#### refuses registration once sealed, so a frame cannot re-probe

- refuses registration once sealed, so a frame cannot re-probe


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses registration once sealed, so a frame cannot re-probe")
var t = kernel_table_new()
kernel_table_seal(t)
assert_true(not kernel_table_register(t, KERNEL_OP_FILL_CONST, 0, 0, 1,
                                      KERNEL_BUCKET_LARGE, 7, true, true))
```

</details>

### span batch — one call, many ops

#### executes a mixed batch and matches per-kernel results

- executes a mixed batch and matches per-kernel results


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("executes a mixed batch and matches per-kernel results")
var dst: [u32] = [0xFF000000; 64]
var src: [u32] = [0x80FFFFFF; 64]
var mask: [u32] = [255; 64]
var t = kernel_table_new()
kernel_table_seal(t)
var batch = span_batch_new(8)
assert_true(span_batch_push(batch, KERNEL_OP_FILL_CONST, 0, 0, 8,
                            0xFF204060, 0))
assert_true(span_batch_push(batch, KERNEL_OP_SRC_OVER_CONST, 8, 0, 8,
                            0x80FF8040, 0))
assert_true(span_batch_push(batch, KERNEL_OP_SRC_OVER_IMAGE, 16, 0, 8,
                            0, 0))
assert_true(span_batch_push(batch, KERNEL_OP_COPY_SPAN, 24, 0, 8, 0, 0))
assert_true(span_batch_push(batch, KERNEL_OP_MASK_SRC_OVER, 32, 0, 8,
                            0xFFFFFFFF, 0))
val n = span_batch_execute(batch, dst, src, mask, t,
                           KERNEL_FORMAT_ARGB8888_STRAIGHT,
                           KERNEL_ALIGN_UNKNOWN, KERNEL_SPAN_CONTIGUOUS)
assert_true(n == 5)
assert_true(dst[0] == 0xFF204060)
assert_true(dst[16] == 0xFF808080)
assert_true(dst[24] == 0x80FFFFFF)
assert_true(dst[32] == 0xFFFFFFFF)
assert_true(t.lookups == 5)
```

</details>

#### REFUSES on overflow rather than growing mid-frame

- REFUSES on overflow rather than growing mid-frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REFUSES on overflow rather than growing mid-frame")
var batch = span_batch_new(2)
assert_true(span_batch_push(batch, KERNEL_OP_FILL_CONST, 0, 0, 1, 0, 0))
assert_true(span_batch_push(batch, KERNEL_OP_FILL_CONST, 1, 0, 1, 0, 0))
assert_true(not span_batch_push(batch, KERNEL_OP_FILL_CONST, 2, 0, 1, 0, 0))
assert_true(batch.overflow_refusals == 1)
assert_true(batch.length == 2)
```

</details>

#### skips non-positive counts without executing them

- skips non-positive counts without executing them


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("skips non-positive counts without executing them")
var dst: [u32] = [0xDEADBEEF; 8]
var src: [u32] = [0; 8]
var mask: [u32] = [0; 8]
var t = kernel_table_new()
var batch = span_batch_new(4)
span_batch_push(batch, KERNEL_OP_FILL_CONST, 0, 0, 0, 0xFF000000, 0)
span_batch_push(batch, KERNEL_OP_FILL_CONST, 0, 0, 0 - 3, 0xFF000000, 0)
val n = span_batch_execute(batch, dst, src, mask, t, 0, 0, 1)
assert_true(n == 0)
assert_true(dst[0] == 0xDEADBEEF)
```

</details>

#### reuses its storage across frames without reallocating

- reuses its storage across frames without reallocating


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reuses its storage across frames without reallocating")
var batch = span_batch_new(4)
span_batch_push(batch, KERNEL_OP_FILL_CONST, 0, 0, 4, 0, 0)
assert_true(batch.length == 1)
span_batch_reset(batch)
assert_true(batch.length == 0)
assert_true(batch.capacity == 4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering exact 8-bit formula — channel layout (contract §1), exact 8-bit formula — src-over (contract §2, §4), exact 8-bit formula — coverage masks (contract §7), clipping (contract §8), kernel set v1 — canonical results, kernel set v1 — copies between distinct buffers, kernel set v1 — overlapping copies (contract §6), kernel registry — per-operation selection, span batch — one call, many ops.
- exact 8-bit formula — channel layout (contract §1)
- exact 8-bit formula — src-over (contract §2, §4)
- exact 8-bit formula — coverage masks (contract §7)
- clipping (contract §8)
- kernel set v1 — canonical results
- kernel set v1 — copies between distinct buffers
- kernel set v1 — overlapping copies (contract §6)
- kernel registry — per-operation selection
- span batch — one call, many ops

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
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

- Canonical SPipe generation for source `46765489904ebdae785c6e40d5f18fa085025b2785b9c3a198f995274465e9b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `46765489904ebdae785c6e40d5f18fa085025b2785b9c3a198f995274465e9b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `46765489904ebdae785c6e40d5f18fa085025b2785b9c3a198f995274465e9b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.spl
mirror: doc/06_spec/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts ARGB channels at their contracted bit positions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips pack against the extractors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pack(alpha,red,green,blue) roundtrips all four channel extractors (F2)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
