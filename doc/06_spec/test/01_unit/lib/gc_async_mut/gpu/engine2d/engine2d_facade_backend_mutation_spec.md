# Engine2D Facade Backend Mutation Specification

> Verifies that the public Engine2D facade delegates clear, filled-rectangle, image blits, clip/mask state, present, and readback through requested software and CPU SIMD backends.

<!-- sdn-diagram:id=engine2d_facade_backend_mutation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine2d_facade_backend_mutation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine2d_facade_backend_mutation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine2d_facade_backend_mutation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D Facade Backend Mutation Specification

Verifies that the public Engine2D facade delegates clear, filled-rectangle, image blits, clip/mask state, present, and readback through requested software and CPU SIMD backends.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/08_tracking/feature/engine2d_trait_facade_backend_execution_2026-06-02.md |
| Design | doc/04_architecture/ui/engine_2d.md |
| Research | doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_facade_backend_mutation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the public Engine2D facade delegates clear, filled-rectangle,
image blits, clip/mask state, present, and readback through requested software
and CPU SIMD backends.

This closes the local, non-platform-specific half of the Engine2D facade
mutation feature request: the production facade must preserve backend pixel
mutations instead of callers reaching into concrete backend implementations.

The scenarios render a reduced 16x16 scene through
`Engine2D.create_with_backend`, read the final framebuffer through
`Engine2D.read_pixels`, and assert concrete pixel values at clear, inside-rect,
and outside-rect coordinates. The CPU SIMD scenario also proves the facade path
reaches the SIMD fill provider by checking the fill hit counter.

## Evidence Model

The spec intentionally avoids direct `SoftwareBackend` or `CpuBackend` calls.
All rendering commands go through `Engine2D.clear`,
`Engine2D.draw_rect_filled`, `Engine2D.draw_image`,
`Engine2D.draw_image_scaled`, `Engine2D.draw_image_transform`,
`Engine2D.set_clip`, `Engine2D.set_mask`, `Engine2D.present`, and
`Engine2D.read_pixels`.

**Requirements:** N/A

**Plan:** doc/08_tracking/feature/engine2d_trait_facade_backend_execution_2026-06-02.md

**Design:** doc/04_architecture/ui/engine_2d.md

**Research:** doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md

## Syntax

Use `std.spec` examples with built-in matchers only. Pixel assertions compare
exact framebuffer values; the SIMD scenario uses `to_be_greater_than(0)` for
the recorded fill hit count.

## Scenarios

### Engine2D facade backend mutation

#### software backend preserves clear and filled rectangle pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_facade_pixels("software")

expect(pixels.len()).to_equal(WIDTH * HEIGHT)
expect(pixels[0]).to_equal(BG)
expect(pixels[5 * WIDTH + 4]).to_equal(FG)
expect(pixels[8 * WIDTH + 9]).to_equal(FG)
expect(pixels[8 * WIDTH + 10]).to_equal(BG)
```

</details>

#### software backend draw_image honors facade clip and mask state

- expect draw image clip mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_draw_image_clip_mask("software")
```

</details>

#### software backend draw_image_scaled honors facade clip and mask state

- expect draw image scaled clip mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_draw_image_scaled_clip_mask("software")
```

</details>

#### software backend draw_image_transform honors facade clip and mask state

- expect draw image transform clip mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_draw_image_transform_clip_mask("software")
```

</details>

#### cpu_simd backend preserves pixels and records SIMD fill use

- reset simd hits
   - Expected: pixels.len() equals `WIDTH * HEIGHT`
   - Expected: pixels[0] equals `BG`
   - Expected: pixels[5 * WIDTH + 4] equals `FG`
   - Expected: pixels[8 * WIDTH + 9] equals `FG`
   - Expected: pixels[8 * WIDTH + 10] equals `BG`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_simd_hits()
val pixels = render_facade_pixels("cpu_simd")

expect(pixels.len()).to_equal(WIDTH * HEIGHT)
expect(pixels[0]).to_equal(BG)
expect(pixels[5 * WIDTH + 4]).to_equal(FG)
expect(pixels[8 * WIDTH + 9]).to_equal(FG)
expect(pixels[8 * WIDTH + 10]).to_equal(BG)
expect(simd_hit_counts().fill_hits).to_be_greater_than(0)
```

</details>

#### cpu_simd backend draw_image honors facade clip and mask state

- expect draw image clip mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_draw_image_clip_mask("cpu_simd")
```

</details>

#### cpu_simd backend draw_image_scaled honors facade clip and mask state

- expect draw image scaled clip mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_draw_image_scaled_clip_mask("cpu_simd")
```

</details>

#### cpu_simd backend draw_image_transform honors facade clip and mask state

- expect draw image transform clip mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_draw_image_transform_clip_mask("cpu_simd")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/08_tracking/feature/engine2d_trait_facade_backend_execution_2026-06-02.md](doc/08_tracking/feature/engine2d_trait_facade_backend_execution_2026-06-02.md)
- **Design:** [doc/04_architecture/ui/engine_2d.md](doc/04_architecture/ui/engine_2d.md)
- **Research:** [doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md](doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md)


</details>
