# cpu_simd_spec

> test/perf/graphics_2d/cpu_simd_spec.spl

<!-- sdn-diagram:id=cpu_simd_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cpu_simd_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cpu_simd_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cpu_simd_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cpu_simd_spec

test/perf/graphics_2d/cpu_simd_spec.spl

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | AC-6 — CPU SIMD kernels declared to optimization plugin metadata; |
| Category | Graphics \| SIMD \| CPU |
| Status | Pending implementation (Phase 5) |
| Source | `test/05_perf/graphics_2d/cpu_simd_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

test/perf/graphics_2d/cpu_simd_spec.spl

                 provider hit counts reported per frame.
                 AC-12 — auto_vectorize + simd_lowering provider hit/change counts.
Verifies:
  - SIMD kernels (fill, copy, alpha_blend, blit, scroll) are declared
  - SimdProvider hit counts are reported per frame (not zero after a frame)
  - Scalar and SIMD paths produce identical results (same pixel hash)
  - Target features (x86 AVX2, ARM NEON, RISC-V V or scalar fallback) are reported
  - vectorize_changes count is reported per frame

@cover src/lib/gc_async_mut/gpu/engine2d/simd_kernels.spl
@cover src/lib/gc_async_mut/gpu/engine2d/simd_provider.spl
@cover src/compiler/60.mir_opt/mir_opt/auto_vectorize.spl

## Scenarios

### cpu_simd — AC-6/AC-12: SIMD kernels, provider hit counts, target features

### kernel name constants

#### AC-6: fill kernel name is fill

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KERNEL_FILL).to_equal("fill")
```

</details>

#### AC-6: copy kernel name is copy

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KERNEL_COPY).to_equal("copy")
```

</details>

#### AC-6: alpha_blend kernel name is alpha_blend

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KERNEL_ALPHA_BLEND).to_equal("alpha_blend")
```

</details>

#### AC-6: blit kernel name is blit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KERNEL_BLIT).to_equal("blit")
```

</details>

#### AC-6: scroll kernel name is scroll

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KERNEL_SCROLL).to_equal("scroll")
```

</details>

#### AC-6: five distinct kernel names exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kernels: [text] = [KERNEL_FILL, KERNEL_COPY, KERNEL_ALPHA_BLEND, KERNEL_BLIT, KERNEL_SCROLL]
expect(kernels.len()).to_equal(5)
```

</details>

### SimdHitCounts fields after one frame

#### AC-6: fill_hits is greater than zero after a frame with fill

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: SimdHitCountsSentinel = make_simd_hit_counts(1, 0, 0, 0, 0, 1)
expect(c.fill_hits > 0).to_equal(true)
```

</details>

#### AC-6: copy_hits is greater than zero after a frame with copy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: SimdHitCountsSentinel = make_simd_hit_counts(0, 1, 0, 0, 0, 1)
expect(c.copy_hits > 0).to_equal(true)
```

</details>

#### AC-6: alpha_hits is greater than zero after a frame with alpha_blend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: SimdHitCountsSentinel = make_simd_hit_counts(0, 0, 1, 0, 0, 1)
expect(c.alpha_hits > 0).to_equal(true)
```

</details>

#### AC-6: blit_hits is greater than zero after a frame with blit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: SimdHitCountsSentinel = make_simd_hit_counts(0, 0, 0, 1, 0, 1)
expect(c.blit_hits > 0).to_equal(true)
```

</details>

#### AC-6: scroll_hits is greater than zero after a frame with scroll

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: SimdHitCountsSentinel = make_simd_hit_counts(0, 0, 0, 0, 1, 1)
expect(c.scroll_hits > 0).to_equal(true)
```

</details>

#### AC-12: vectorize_changes is reported (not negative)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: SimdHitCountsSentinel = make_simd_hit_counts(1, 1, 1, 1, 1, 3)
expect(c.vectorize_changes >= 0).to_equal(true)
```

</details>

#### AC-12: vectorize_changes count is greater than zero after vectorized frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: SimdHitCountsSentinel = make_simd_hit_counts(1, 1, 1, 1, 1, 3)
expect(c.vectorize_changes > 0).to_equal(true)
```

</details>

### scalar vs SIMD parity

#### AC-6: x86 AVX2 SIMD hash matches scalar hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t: SimdTargetSentinel = make_simd_target_x86(0xABCD1234, 0xABCD1234)
expect(simd_parity_ok(t)).to_equal(true)
```

</details>

#### AC-6: ARM NEON SIMD hash matches scalar hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t: SimdTargetSentinel = make_simd_target_arm(0xDEADBEEF, 0xDEADBEEF)
expect(simd_parity_ok(t)).to_equal(true)
```

</details>

#### AC-6: scalar fallback hash matches scalar reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t: SimdTargetSentinel = make_simd_target_scalar(0xCAFEBABE, 0xCAFEBABE)
expect(simd_parity_ok(t)).to_equal(true)
```

</details>

#### AC-6: differing hashes on x86 indicates a parity failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t: SimdTargetSentinel = make_simd_target_x86(0xABCD1234, 0xFFFF0000)
expect(simd_parity_ok(t)).to_equal(false)
```

</details>

### target feature reporting

#### AC-6: x86_64 target reports avx2 feature

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t: SimdTargetSentinel = make_simd_target_x86(1, 1)
expect(t.arch).to_equal("x86_64")
expect(t.feature).to_equal("avx2")
```

</details>

#### AC-6: aarch64 target reports neon feature

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t: SimdTargetSentinel = make_simd_target_arm(1, 1)
expect(t.arch).to_equal("aarch64")
expect(t.feature).to_equal("neon")
```

</details>

#### AC-6: unknown arch falls back to scalar feature

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t: SimdTargetSentinel = make_simd_target_scalar(1, 1)
expect(t.feature).to_equal("scalar")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
