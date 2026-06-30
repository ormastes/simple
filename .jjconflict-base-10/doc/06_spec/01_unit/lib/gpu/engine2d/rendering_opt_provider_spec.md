# Rendering Opt Provider Specification

> <details>

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
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rendering Opt Provider Specification

## Scenarios

### Engine2D SIMD rendering optimization provider metadata

#### maps SIMD kernel hits into one provider hit counter

- reset simd hits
- record simd fill hit
- record simd copy hit
- record simd alpha hit
- record simd blit hit
- record simd scroll hit
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

- reset simd hits
- record simd fill hit
- record simd vectorize change
- record simd vectorize change
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

- reset simd hits
- register simd provider
- record simd scroll hit
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

- reset simd hits
- record simd fill hit
- record simd copy hit
- record simd vectorize change
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

#### keeps provider stats wire text stable

- provider record hit
- provider record hit
- provider record miss
- provider record change
   - Expected: provider.stats() equals `Provider[id=pipeline_cache.metal kind=pipeline_cache arch=metal features=msl ... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val provider = RenderingOptProvider.create("pipeline_cache", "metal", "msl")
provider.record_hit()
provider.record_hit()
provider.record_miss()
provider.record_change()

expect(provider.stats()).to_equal("Provider[id=pipeline_cache.metal kind=pipeline_cache arch=metal features=msl hits=2 misses=1 changes=1 hit_rate=66% active=true]")
```

</details>

#### keeps report summary wire text stable

- simd record hit
- shader record miss
- var report = RenderingOptReport create
   - Expected: report.add_provider(simd) equals `ok`
   - Expected: report.add_provider(shader) equals `ok`
   - Expected: report.summary() equals `RenderingOptReport[providers=2 total_hits=1 total_misses=1 total_changes=0 p0... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simd = RenderingOptProvider.create("simd_vectorization", "x86_64", "avx2")
simd.record_hit()
val shader = RenderingOptProvider.shader_provider("vulkan")
shader.record_miss()
var report = RenderingOptReport.create()

expect(report.add_provider(simd)).to_equal("ok")
expect(report.add_provider(shader)).to_equal("ok")

expect(report.summary()).to_equal("RenderingOptReport[providers=2 total_hits=1 total_misses=1 total_changes=0 p0=[simd_vectorization.x86_64 simd_vectorization h=1 m=0] p1=[shader_specialization.vulkan shader_specialization h=0 m=1]]")
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
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
