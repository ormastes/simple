# LLM-First Simple Frame Capture / Replay Debugger

**Date:** 2026-06-16
**Domain:** ui / capture_replay
**Status:** Research — final report / executive decision

Related: [`../draw_ir/draw_io_sdn_draw_ir.md`](../draw_ir/draw_io_sdn_draw_ir.md),
[`../render_path/gui_web_2d_render_optimization_2026-06-16.md`](../render_path/gui_web_2d_render_optimization_2026-06-16.md)

---

## Executive decision

RDC (RenderDoc capture) is **not** the best primary format for Simple. It is
excellent for deep GPU/API debugging, but too low-level and verbose for
LLM-driven diagnosis. The best architecture is a **tiered capture system**:

```
Default artifact for LLM:
  .sdcap.md / .sdcap.sdn     compact semantic summary

Default artifact for deterministic replay:
  .sdcap.bin                 exact Draw IR / Engine2D replay payload

Optional deep-debug artifact:
  .gfxr / .rdc / Vulkan-layer trace
```

The project should build an **RDC-like CLI experience, not an RDC-compatible
clone** at first. The tool should feel like `renderdoccmd` / `gfxrecon-*`, but
its first-class capture unit should be **Simple Draw IR**, not raw Vulkan calls.

Recommended names:

```
CLI:        simple-capture
Viewer:     simple-inspect
Format:     .sdcap
Report:     .sdcap.md
Deep mode:  .sdcap.detail/
```

The key reason: Simple already has the correct semantic boundary. The canonical
UI stack says Simple owns UI semantics and event ownership, introduces a typed
render/draw IR boundary, and lets a render-optimization plugin accelerate draw
batches without taking over GUI policy. Render IR already carries style,
surfaces, text runs, images, dirty regions, screen config, and callback ids;
Draw IR carries composed batches, composition, callback locality, and
source/style provenance.

---

## Research summary

**RenderDoc's** model is frame capture + replay + inspection. Its quick-start
workflow launches an executable, injects capture hooks, and captures a frame by
hotkey; the UI then exposes texture viewing, event browsing, API-call
inspection, timeline, pipeline state, and mesh/buffer inspection. Its Event
Browser presents draw/dispatch/resource actions chronologically, and the API
Inspector shows API calls and parameters for the selected event. Its Python API
exposes a low-level replay interface for capture files, frame replay, resources,
texture/buffer data, event ids, structured call data, and pipeline state.

**GFXReconstruct** is the closer reference for a CLI capture/replay system. It
captures graphics API calls, stores them in capture files, and replays them
later to reconstruct graphics behavior. Its Vulkan path uses
`VK_LAYER_LUNARG_gfxreconstruct`, plus tools such as `gfxrecon-replay`,
`gfxrecon-info`, `gfxrecon-compress`, `gfxrecon-extract`, `gfxrecon-convert`,
and `gfxrecon-optimize`. The Vulkan capture layer is enabled through the Vulkan
loader using `VK_LAYER_PATH`, `VK_INSTANCE_LAYERS`, or application-level layer
enablement. It supports frame-range captures, hotkey triggers, compression,
capture-file naming, mapped-memory tracking modes, and replay screenshots.

**Vulkan** itself supports this style through loader layers. The loader
distinguishes implicit and explicit layers; implicit layers can be enabled
automatically, while explicit layers must be requested. Layer discovery is
manifest-based on desktop platforms, and environment variables such as
`VK_LAYER_PATH`, `VK_ADD_LAYER_PATH`, `VK_LOADER_LAYERS_ENABLE`, and
`VK_INSTANCE_LAYERS` affect layer discovery/activation.

**The lesson for Simple:** copy the workflow, not the verbosity.
RenderDoc/GFXReconstruct are valuable references for capture/replay UX, but
Simple should capture the **semantic render contract** first.

---

## Why RDC is too verbose for LLM

RDC-level capture answers questions like:

- What was bound to descriptor set 2?
- What was the fragment shader?
- Which texture was read by this draw?
- What was the pipeline state at event 3812?

An LLM debugging Simple usually needs questions like:

- Which UI node changed?
- Which Draw IR command produced the wrong pixels?
- Was the dirty region too small?
- Was this rect skipped because of visibility?
- Did CPU and Vulkan backends disagree?
- Which style/layout revision invalidated the cache?

Those are **semantic** questions. Raw Vulkan calls obscure them.

Simple already defines Draw IR v2 with schema version, command kinds, source
info, batches, compositions, backend targets, fallback reasons, geometry rects,
computed style, parent ids, images, paths, edges, and event-target context. The
Draw.io-compatible Draw IR plan explicitly says the canonical interchange text
is **SDN**, not JSON/YAML, and that capture/stringification must be skipped when
the flag is off. That is already LLM-friendly.

So the best design is:

```
LLM sees:
  summarized semantic Draw IR
  compact dirty-region report
  exact failing commands
  visual diff metadata
  selected pixel evidence
  fallback/backend decisions

Machine sees:
  exact binary replay payload
  full resources
  framebuffer images
  backend traces
```

---

## Suggested architecture

```
Simple app / test / QEMU / GUI host
        |
        v
Capture trigger
        |
        v
SimpleCaptureSession
        |
        +--> Semantic capture lane
        |      GUI AST revision
        |      WebRender IR snapshot/diff
        |      Draw IR composition/diff
        |      dirty regions
        |      style/layout/font/image revisions
        |      event/callback provenance
        |
        +--> Engine2D command lane
        |      clear
        |      draw_rect_filled
        |      draw_rect
        |      draw_line
        |      draw_circle
        |      draw_text
        |      blit
        |      scroll
        |      present
        |
        +--> Surface lane
        |      final framebuffer
        |      intermediate surfaces
        |      glyph atlas snapshot
        |      image atlas snapshot
        |
        +--> Backend lane
               CPU replay evidence
               Vulkan/Metal/WebGPU replay evidence
               optional GFXR/RDC capture pointer
```

This fits the repo's current design. The optimization research says Simple
should keep semantic UI, event routing, layout ownership, dirty-region truth,
and CPU fallback in Simple, while accelerating Draw IR batches, compositing,
glyph/image/filter processing, and large pixel operations through Engine2D/GPU
backends. It also says Simple already owns widget tree, GUI AST, event ids,
focus, layout policy, accessibility, dirty-region truth, cache invalidation,
typed WebRender IR/Draw IR, CPU fallback, and conformance tests.

The capture system should therefore be implemented **above Vulkan first**.

---

## Capture levels

Use explicit detail levels. This solves the "LLM too verbose" problem while
still supporting deep debugging.

```
Level 0: hash
  frame hash only
  pass/fail metadata
  screenshot path

Level 1: summary
  LLM-first .sdcap.md
  changed nodes
  dirty regions
  command counts
  failed diff summary
  top suspicious commands

Level 2: draw-ir
  complete DrawIrComposition
  Draw IR diff
  source/style/layout provenance
  enough to replay in CPU backend

Level 3: engine2d
  exact Engine2D command stream
  surfaces/resources used by Simple 2D
  CPU/SIMD replay image
  backend replay image

Level 4: backend
  backend batches
  pipeline/cache/fallback decisions
  shader/kernel names
  texture/atlas resource ids
  sync/readback evidence

Level 5: api-trace
  optional Vulkan/GFXReconstruct/RenderDoc artifact
  only for GPU/backend/driver bugs
```

Default for CI and LLM:

```
simple-capture --level summary
simple-capture --level draw-ir
```

Use deep mode only when necessary:

```
simple-capture --level backend
simple-capture --level api-trace --with-gfxr
simple-capture --level api-trace --with-renderdoc
```

---

## File layout

Recommended capture artifact:

```
fail_2026_06_16_153012.sdcap/
  manifest.sdn
  summary.md
  draw_ir.sdn
  draw_ir.diff.sdn
  engine2d.commands.sdn
  frame.final.png
  frame.expected.png
  frame.diff.png
  surfaces/
    surface_main.argb.zst
    glyph_atlas_0.png
    image_atlas_0.png
  replay/
    cpu.png
    vulkan.png
    diff_cpu_vulkan.png
  detail/
    batches.sdn
    backend_plan.sdn
    fallback.sdn
    timing.sdn
  external/
    frame.gfxr        optional
    frame.rdc         optional
```

For Git/PR/LLM, attach only:

```
summary.md
draw_ir.diff.sdn
frame.diff.png
```

For deterministic local reproduction, use the full directory or `.sdcap.bin`.

---

## LLM-first summary format

The LLM report must be **bounded, ranked, and semantic**. Example:

```
# Simple Capture Summary

capture_id: cap_20260616_153012
test: test/03_system/app/ui_web/editor_cursor_spec.spl
frame: 152
screen: 1920x1080
backend: vulkan
reference_backend: cpu_simd
result: FAIL

## Failure
frame_hash:
  expected: a92f10c2
  actual:   c31b8839

pixel_diff:
  changed_pixels: 184
  bounding_box: [412,80,2,18]
  max_delta: 17
  likely_node: editor.cursor

## Changed semantic nodes
1. editor.cursor
   source: gui_ast
   style_rev: 44 -> 45
   layout_rev: unchanged
   command: fill_rect
   expected_color: #ffffff
   actual_color: #eeeeee

## Dirty regions
- [412,80,2,18] reason=caret_blink
- [0,0,0,0] no full-frame repaint

## Suspicious commands
1. cmd_088 fill_rect editor.cursor
   bbox=[412,80,2,18]
   backend=vulkan
   cpu_color=#ffffff
   gpu_color=#eeeeee
   suspicion=backend_blend_or_color_pack
```

This is the artifact an LLM can reason over.

---

## Detail-mode SDN schema

The detailed SDN should preserve exact replay data without flooding the default
report.

```
capture
    version simple-capture-v1
    id cap_20260616_153012
    frame 152
    level draw-ir
    schema simple-draw-ir-v2
    screen
        width 1920
        height 1080
        format argb8888
    source
        surface main
        gui_ast_rev 918
        style_rev 45
        layout_rev 120
        font_rev 8
        image_rev 13
    backend
        requested auto
        selected vulkan
        reference cpu_simd

dirty_regions
    rect 412 80 2 18
        reason caret_blink
        source editor.cursor

commands
    command cmd_088
        kind rect
        component_id editor.cursor
        source_kind gui_ast
        x 412
        y 80
        width 2
        height 18
        color 0xffffffff
        style_rev 45
        layout_rev 120
        batch editor_layer
        backend_target gpu
        fallback_required false
```

Draw IR already has component_id, command geometry, command kind, computed
style, source info, batch info, backend target, and composition structure. The
Draw IR plan also already includes Protocol-v2 inspection endpoints, SDN/JSON
Draw IR output, `expect_draw`, and baseline diff reports.

---

## RDC-like CLI plan

The CLI should feel like GFXReconstruct/RenderDoc, but use Simple semantics.

### Core commands

```
simple-capture run ./simple_app -- --open examples/ui/editor.spl
simple-capture run --frame 152 --level summary ./simple_app
simple-capture run --frames 150-160 --level draw-ir ./simple_app
simple-capture trigger --hotkey F12 --level draw-ir ./simple_app

simple-capture info fail.sdcap
simple-capture summarize fail.sdcap --for-llm
simple-capture replay fail.sdcap --backend cpu
simple-capture replay fail.sdcap --backend vulkan
simple-capture diff fail.sdcap --expected baseline.sdcap
simple-capture inspect fail.sdcap
simple-capture export fail.sdcap --format sdn
simple-capture export fail.sdcap --format markdown
simple-capture pack fail.sdcap --output fail.sdcap.bin
simple-capture unpack fail.sdcap.bin
```

### Deep mode commands

```
simple-capture run --level backend ./simple_app
simple-capture run --level api-trace --with-gfxr ./simple_app
simple-capture run --level api-trace --with-renderdoc ./simple_app

simple-capture attach --pid 12345 --level summary
simple-capture queue --frame 300 --level draw-ir
simple-capture trim fail.sdcap --frames 152-153
simple-capture minimize fail.sdcap --keep-node editor.cursor
```

### CI commands

```
simple-capture test test/03_system/app/ui_web/editor_cursor_spec.spl \
  --on-fail summary \
  --artifact-dir artifacts/simple-capture

simple-capture assert fail.sdcap \
  --max-diff-pixels 0 \
  --require-cpu-gpu-match \
  --require-no-fallback
```

### LLM command

```
simple-capture summarize fail.sdcap \
  --for-llm \
  --budget 12000 \
  --include-top 20 \
  --include-images \
  --redact-text
```

Output:

```
summary.md
draw_ir.diff.sdn
frame.diff.png
```

---

## Internal module plan

```
src/lib/common/ui/capture/
  capture_manifest.spl
  capture_level.spl
  capture_writer.spl
  capture_reader.spl
  capture_redaction.spl
  capture_summary.spl

src/lib/common/ui/capture/draw_ir/
  draw_ir_capture.spl
  draw_ir_delta.spl
  draw_ir_minimize.spl
  draw_ir_suspicion.spl

src/lib/nogc_sync_mut/gpu/engine2d/capture/
  engine2d_recorder.spl
  engine2d_replay_cpu.spl
  engine2d_replay_compare.spl

src/lib/gc_async_mut/gpu/engine2d/capture/
  backend_capture_plan.spl
  vulkan_capture_bridge.spl
  external_trace_bridge.spl

src/app/simple_capture/
  main.spl
  cmd_run.spl
  cmd_info.spl
  cmd_replay.spl
  cmd_diff.spl
  cmd_summarize.spl
  cmd_pack.spl
  cmd_inspect.spl
```

**Important:** put the core format and summary logic in
`src/lib/common/ui/capture`, not in the app, so CI/tests/QEMU can use it.

---

## Capture trigger architecture

```
CaptureTrigger
  by_frame(frame_id)
  by_failure(test_id)
  by_hotkey(key)
  by_api(endpoint)
  by_env(SIMPLE_CAPTURE=...)
  by_programmatic_marker(name)

CaptureSession
  begin_frame(frame_id)
  record_render_ir(...)
  record_draw_ir(...)
  record_engine2d_command(...)
  record_surface(...)
  record_backend_plan(...)
  end_frame()
  write_artifact()
```

Environment examples:

```
SIMPLE_CAPTURE=1
SIMPLE_CAPTURE_LEVEL=summary
SIMPLE_CAPTURE_FRAME=152
SIMPLE_CAPTURE_DIR=artifacts/capture
SIMPLE_CAPTURE_REDACT_TEXT=1
SIMPLE_CAPTURE_EXTERNAL=gfxr
```

---

## Replay architecture

```
.sdcap
  |
  v
CaptureReader
  |
  +--> DrawIrReplay
  |      validates schema
  |      rebuilds DrawIrComposition
  |      executes CPU oracle
  |
  +--> Engine2DReplay
  |      replays command stream
  |      emits framebuffer
  |
  +--> BackendReplay
         runs selected backend if available
         compares output to CPU oracle
```

The repo's Engine2D QEMU architecture already has deterministic primitive
behavior and screenshot/baseline policy: primitives such as `clear`,
`draw_rect_filled`, `draw_rect`, `draw_line`, `draw_circle_filled`,
`draw_circle`, and `present` are locked, deterministic ARGB colors are asserted,
and baselines are not silently refreshed. This makes Engine2D command capture a
safe replay layer.

---

## Comparison with RenderDoc / GFXReconstruct

```
RenderDoc:
  best for manual GPU frame inspection
  strong UI
  pipeline/texture/buffer/event inspection
  not semantic to Simple

GFXReconstruct:
  best reference for CLI capture/replay
  Vulkan layer based
  good for API-call replay and screenshots
  still too low-level for LLM

Simple Capture:
  best for Simple UI/Draw IR failures
  semantic, small, diffable
  deterministic CPU oracle
  can escalate to Vulkan/GFXR/RDC when needed
```

GFXReconstruct already proves that a CLI capture/replay tool can support frame
ranges, hotkeys, compression, replay screenshots, offscreen swapchain replay,
and capture processing tools. Simple should adopt those UX patterns, but the
capture payload should be **Draw IR first**.

---

## What not to build first

Do not start with:

- full Vulkan layer
- full RDC parser/writer
- full pipeline-state UI
- shader debugger
- mesh viewer
- descriptor inspector
- global GPU memory capture

That path will consume a lot of time and produce artifacts that still cannot
explain Simple-specific bugs.

Start with:

- Draw IR capture
- Draw IR diff
- Engine2D command recorder
- CPU replay
- CPU vs backend image diff
- LLM summary generator

This is smaller, repo-aligned, and immediately useful.

---

## Acceptance criteria

### Phase 1: LLM summary

Done when a failing UI/2D test emits `summary.md`, `draw_ir.diff.sdn`,
`frame.final.png`, `frame.diff.png`, and the summary includes: test name, frame
id, backend, expected/actual hash, dirty regions, changed Draw IR nodes, top
suspicious commands, fallback reasons, and CPU/backend comparison.

### Phase 2: exact Draw IR replay

Done when `simple-capture replay fail.sdcap --backend cpu` reproduces the
captured final framebuffer hash.

### Phase 3: Engine2D command replay

Done when captured Engine2D commands replay deterministically for: `clear`,
fill, rect outline, line, circle, text placeholder or glyph run, blit, scroll,
present.

### Phase 4: backend comparison

Done when `simple-capture replay fail.sdcap --backend vulkan` and
`simple-capture diff fail.sdcap --cpu --vulkan` report pixel-equivalent output
or a bounded diff.

### Phase 5: external trace bridge

Done when `simple-capture run --level api-trace --with-gfxr ./simple_app` stores
a `.gfxr` pointer under `external/`, while `summary.md` still remains the primary
LLM artifact.

---

## Final recommendation

Build **Simple Capture, not "Simple RenderDoc"** first.

Policy:

```
default:
  semantic Draw IR capture

debug:
  Engine2D command capture

deep:
  backend resource/batch capture

last resort:
  Vulkan/GFXR/RDC capture
```

The best final architecture is:

```
Simple UI semantics
  -> WebRender IR
  -> Draw IR
  -> SimpleCapture semantic recorder
  -> Engine2D recorder
  -> CPU oracle replay
  -> backend replay
  -> LLM summary + exact binary capture
  -> optional external GPU trace
```

That gives you the important RenderDoc/RDC experience — capture, replay, inspect,
diff, export — without forcing the LLM to read raw graphics API noise.
