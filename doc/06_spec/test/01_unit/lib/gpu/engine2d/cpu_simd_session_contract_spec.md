# CPU SIMD Session Contract Specification

> Verifies the CPU SIMD Engine2D compute-session lifecycle and shared operation contract used as the software-side compute lane for fill, copy, alpha, blit, and scroll operations.

<!-- sdn-diagram:id=cpu_simd_session_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cpu_simd_session_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cpu_simd_session_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cpu_simd_session_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CPU SIMD Session Contract Specification

Verifies the CPU SIMD Engine2D compute-session lifecycle and shared operation contract used as the software-side compute lane for fill, copy, alpha, blit, and scroll operations.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Reference | `src/lib/nogc_sync_mut/gpu/engine2d/cpu_simd_session.spl` |
| Requirements | N/A |
| Plan | doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md |
| Design | doc/05_design/ui/renderer_unification_2026-06-15.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md |
| Source | `test/01_unit/lib/gpu/engine2d/cpu_simd_session_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the CPU SIMD Engine2D compute-session lifecycle and shared operation
contract used as the software-side compute lane for fill, copy, alpha, blit,
and scroll operations.

**Source:** `src/lib/nogc_sync_mut/gpu/engine2d/cpu_simd_session.spl`
**Requirements:** N/A
**Research:** doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md
**Plan:** doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md
**Design:** doc/05_design/ui/renderer_unification_2026-06-15.md

## Syntax

Create `CpuSimdSession.create("auto")`, initialize it, run compute-session
operations, and inspect `hit_counts()` for SIMD delegation evidence.

## Examples

The scenarios verify lifecycle behavior, SIMD-backed operation hit counts, and
GPU-only module/kernel hooks remaining harmless CPU no-ops.

## Scenarios

### CpuSimdSession compute contract

#### reports CPU SIMD kind availability and safe lifecycle

- var session = CpuSimdSession create
   - Expected: session.kind().kind equals `BackendSessionKind.cpu_simd().kind`
   - Expected: session.is_available() is true
- session shutdown
   - Expected: session.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = CpuSimdSession.create("auto")

expect(session.kind().kind).to_equal(BackendSessionKind.cpu_simd().kind)
expect(session.is_available()).to_equal(true)
expect(session.init()).to_be_nil()
expect(session.synchronize()).to_be_nil()
session.shutdown()
expect(session.initialized).to_equal(false)
```

</details>

#### delegates fill copy alpha blit and scroll operations to SIMD kernels

- reset simd hits
- var session = CpuSimdSession create
   - Expected: pixels[0] equals `0xFF010203`
   - Expected: pixels[3] equals `0xFF010203`
   - Expected: pixels[4] equals `0xFF112233`
   - Expected: pixels[7] equals `0xFF112233`
   - Expected: pixels[12] equals `0xFF112233`
   - Expected: pixels[4] equals `0xFF010203`
   - Expected: hits.fill_hits equals `1`
   - Expected: hits.copy_hits equals `1`
   - Expected: hits.alpha_hits equals `1`
   - Expected: hits.blit_hits equals `1`
   - Expected: hits.scroll_hits equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_simd_hits()
var session = CpuSimdSession.create("auto")
expect(session.init()).to_be_nil()

var pixels: [u32] = [0u32; 16]
var src: [u32] = [0xFF112233; 16]
var alpha_src: [u32] = [0x80FF0000; 16]

expect(session.fill(pixels, 0, 4, 0xFF010203)).to_be_nil()
expect(pixels[0]).to_equal(0xFF010203)
expect(pixels[3]).to_equal(0xFF010203)

expect(session.copy(pixels, 4, src, 0, 4)).to_be_nil()
expect(pixels[4]).to_equal(0xFF112233)
expect(pixels[7]).to_equal(0xFF112233)

expect(session.alpha_blend(pixels, alpha_src, 8, 4)).to_be_nil()
expect(pixels[8]).to_be_greater_than(0)

expect(session.blit_rect(pixels, 4, 0, 3, src, 4, 0, 0, 4, 1)).to_be_nil()
expect(pixels[12]).to_equal(0xFF112233)

expect(session.scroll(pixels, 4, 0, 0, 4, 4, 1)).to_be_nil()
expect(pixels[4]).to_equal(0xFF010203)

val hits = session.hit_counts()
expect(hits.fill_hits).to_equal(1)
expect(hits.copy_hits).to_equal(1)
expect(hits.alpha_hits).to_equal(1)
expect(hits.blit_hits).to_equal(1)
expect(hits.scroll_hits).to_equal(1)
```

</details>

#### treats GPU-only module and kernel hooks as CPU no-ops

- var session = CpuSimdSession create


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = CpuSimdSession.create("auto")
expect(session.init()).to_be_nil()

expect(session.load_module("unused", "ptx")).to_be_nil()
expect(session.launch_kernel("unused", 1, 1, 1, 1)).to_be_nil()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md](doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md)
- **Design:** [doc/05_design/ui/renderer_unification_2026-06-15.md](doc/05_design/ui/renderer_unification_2026-06-15.md)
- **Research:** [doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md](doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md)


</details>
