# Graphics Session Specification

> <details>

<!-- sdn-diagram:id=graphics_session_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=graphics_session_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

graphics_session_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=graphics_session_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Graphics Session Specification

## Scenarios

### GraphicsSession API

#### creates managed sessions inactive

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = GraphicsSession.make(1, "managed_shared")
expect(s.mode).to_equal("managed_shared")
expect(s.active).to_equal(false)
```

</details>

#### rejects sharing perf exclusive sessions twice

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = GraphicsSession.make(2, "perf_exclusive")
val first = s.retain()
val second = s.retain()
expect(first).to_equal("")
expect(second).to_equal("error:mode_conflict")
```

</details>

#### begins a frame after retain

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = GraphicsSession.make(1, "managed_shared")
val ret = s.retain()
val frame = s.begin_frame()
expect(ret).to_equal("")
expect(frame).to_equal(1)
```

</details>

### GraphicsSession surfaces

#### keeps legacy 2D constructors in legacy no-session mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = LegacyEngine2D.create(1920, 1080)
expect(e.backend).to_equal("legacy_no_session")
expect(e.fill_rect(0, 0, 100, 100, 0)).to_equal("fill_rect")
```

</details>

#### keeps legacy 3D constructors in legacy no-session mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = LegacyEngine3D.create(1280, 720)
expect(e.backend).to_equal("legacy_no_session")
expect(e.draw_mesh(1, 2)).to_equal("draw_mesh")
```

</details>

#### supports managed 2D game sprite sessions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = Game2DSession.create_managed(1280, 720)
expect(g.mode).to_equal("managed_shared")
expect(g.add_sprite(10, 20, 64, 64, 1)).to_equal(1)
```

</details>

#### supports perf-exclusive 3D game asset sessions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = Game3DSession.create_perf(1920, 1080)
expect(g.mode).to_equal("perf_exclusive")
expect(g.load_asset("mesh.obj", "mesh")).to_equal(1)
```

</details>

#### shares managed policy across web, GUI, and WM surfaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val web = WebRendererSession.create_managed(1)
val gui = GuiAppSession.create_managed()
val wm = WmCompositorSession.create_managed()
expect(web.mode).to_equal("managed_shared")
expect(gui.mode).to_equal("managed_shared")
expect(wm.mode).to_equal("managed_shared")
```

</details>

### GraphicsSession optimization providers

#### persists provider facts by incrementing fact count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = GraphicsOptProvider.create("test", "shader", "vulkan")
expect(p.add_fact("simd_width", "256")).to_equal(1)
expect(p.add_fact("arch", "x86_64")).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | Active |
| Source | `test/01_unit/gpu/graphics_session_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GraphicsSession API
- GraphicsSession surfaces
- GraphicsSession optimization providers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
