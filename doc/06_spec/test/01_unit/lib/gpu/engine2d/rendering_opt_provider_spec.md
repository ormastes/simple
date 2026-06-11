# Rendering Opt Provider Specification

> 1. reset simd hits

<!-- sdn-diagram:id=rendering_opt_provider_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rendering_opt_provider_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rendering_opt_provider_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rendering_opt_provider_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rendering Opt Provider Specification

## Scenarios

### Engine2D SIMD rendering optimization provider metadata

#### maps SIMD kernel hits into one provider hit counter

1. reset simd hits
2. record simd fill hit
3. record simd copy hit
4. record simd alpha hit
5. record simd blit hit
6. record simd scroll hit
   - Expected: provider.provider_kind equals `simd_vectorization`
   - Expected: provider.target_arch equals `x86_64`
   - Expected: provider.target_features equals `avx2`
   - Expected: provider.hit_count equals `5`
   - Expected: provider.change_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_simd_hits()
record_simd_fill_hit()
record_simd_copy_hit()
record_simd_alpha_hit()
record_simd_blit_hit()
record_simd_scroll_hit()

val provider = rendering_opt_provider_from_simd_counts("x86_64", "avx2", simd_hit_counts())

expect(provider.provider_kind).to_equal("simd_vectorization")
expect(provider.target_arch).to_equal("x86_64")
expect(provider.target_features).to_equal("avx2")
expect(provider.hit_count).to_equal(5)
expect(provider.change_count).to_equal(0)
```

</details>

#### maps vectorization change events into provider change counter

1. reset simd hits
2. record simd fill hit
3. record simd vectorize change
4. record simd vectorize change
   - Expected: provider.hit_count equals `1`
   - Expected: provider.change_count equals `2`
   - Expected: provider.target_arch equals `aarch64`
   - Expected: provider.target_features equals `neon`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_simd_hits()
record_simd_fill_hit()
record_simd_vectorize_change()
record_simd_vectorize_change()

val provider = current_simd_rendering_opt_provider("aarch64", "neon")

expect(provider.hit_count).to_equal(1)
expect(provider.change_count).to_equal(2)
expect(provider.target_arch).to_equal("aarch64")
expect(provider.target_features).to_equal("neon")
```

</details>

#### uses registered provider identity in optimization metadata

1. reset simd hits
2. register simd provider
3. record simd scroll hit
   - Expected: provider.provider_id equals `cpu_simd_frame_provider`
   - Expected: provider.hit_count equals `1`
   - Expected: provider.target_arch equals `riscv64`
   - Expected: provider.target_features equals `rvv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_simd_hits()
register_simd_provider("cpu_simd_frame_provider")
record_simd_scroll_hit()

val provider = current_simd_rendering_opt_provider("riscv64", "rvv")

expect(provider.provider_id).to_equal("cpu_simd_frame_provider")
expect(provider.hit_count).to_equal(1)
expect(provider.target_arch).to_equal("riscv64")
expect(provider.target_features).to_equal("rvv")
```

</details>

#### builds a frame report from current SIMD counters

1. reset simd hits
2. record simd fill hit
3. record simd copy hit
4. record simd vectorize change
   - Expected: report.provider_count equals `1`
   - Expected: report.total_hits equals `2`
   - Expected: report.total_changes equals `1`
   - Expected: report.p0_kind equals `simd_vectorization`
   - Expected: report.p0_hits equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_simd_hits()
record_simd_fill_hit()
record_simd_copy_hit()
record_simd_vectorize_change()

val report = rendering_opt_report_from_simd("x86_64", "avx2")

expect(report.provider_count).to_equal(1)
expect(report.total_hits).to_equal(2)
expect(report.total_changes).to_equal(1)
expect(report.p0_kind).to_equal("simd_vectorization")
expect(report.p0_hits).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/rendering_opt_provider_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D SIMD rendering optimization provider metadata

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
