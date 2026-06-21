# Engine2D Trait Facade Backend Execution Specification

> Verifies that the canonical `Engine2D` facade preserves backend pixel mutations for the reduced renderer-parity scene instead of losing state behind trait-field dispatch.

<!-- sdn-diagram:id=engine2d_trait_facade_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine2d_trait_facade_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine2d_trait_facade_backend_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine2d_trait_facade_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D Trait Facade Backend Execution Specification

Verifies that the canonical `Engine2D` facade preserves backend pixel mutations for the reduced renderer-parity scene instead of losing state behind trait-field dispatch.

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | Active |
| Requirements | doc/02_requirements/ui/misc/shared_wm_renderer_unification.md |
| Plan | doc/08_tracking/feature/engine2d_trait_facade_backend_execution_2026-06-02.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | doc/09_report/shared_wm_renderer_unification_evidence_2026-06-04.md |
| Source | `test/01_unit/gpu/engine2d_trait_facade_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the canonical `Engine2D` facade preserves backend pixel mutations
for the reduced renderer-parity scene instead of losing state behind trait-field
dispatch.

**Feature:** doc/08_tracking/feature/engine2d_trait_facade_backend_execution_2026-06-02.md
**Requirements:** doc/02_requirements/ui/misc/shared_wm_renderer_unification.md
**Research:** doc/09_report/shared_wm_renderer_unification_evidence_2026-06-04.md
**Plan:** doc/08_tracking/feature/engine2d_trait_facade_backend_execution_2026-06-02.md
**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Syntax

Use `Engine2D.create_with_backend(width, height, backend_name)`, then draw
through `Engine2D.clear`, `Engine2D.draw_rect_filled`, `Engine2D.present`, and
verify `Engine2D.read_pixels`.

## Examples

The reduced scene clears a 16x16 framebuffer to `0xFF102030`, draws a 4x4
filled rectangle at `(4, 4)` with `0xFF010204`, and checks one background pixel
plus one rectangle pixel.

## Scenarios

### Engine2D trait facade backend execution

#### preserves software backend pixel mutations through the facade

- Create the software Engine2D backend facade
- Draw the reduced clear plus filled-rectangle scene through Engine2D
- Read back facade pixels and verify the software mutation survived
- expect reduced scene


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create the software Engine2D backend facade")
step("Draw the reduced clear plus filled-rectangle scene through Engine2D")
step("Read back facade pixels and verify the software mutation survived")
expect_reduced_scene("software")
```

</details>

#### preserves cpu_simd backend pixel mutations through the facade

- Create the cpu_simd Engine2D backend facade
- Draw the reduced clear plus filled-rectangle scene through Engine2D
- Read back facade pixels and verify the cpu_simd mutation survived
- expect reduced scene


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create the cpu_simd Engine2D backend facade")
step("Draw the reduced clear plus filled-rectangle scene through Engine2D")
step("Read back facade pixels and verify the cpu_simd mutation survived")
expect_reduced_scene("cpu_simd")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/ui/misc/shared_wm_renderer_unification.md](doc/02_requirements/ui/misc/shared_wm_renderer_unification.md)
- **Plan:** [doc/08_tracking/feature/engine2d_trait_facade_backend_execution_2026-06-02.md](doc/08_tracking/feature/engine2d_trait_facade_backend_execution_2026-06-02.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)
- **Research:** [doc/09_report/shared_wm_renderer_unification_evidence_2026-06-04.md](doc/09_report/shared_wm_renderer_unification_evidence_2026-06-04.md)


</details>
