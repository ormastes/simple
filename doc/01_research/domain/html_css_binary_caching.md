<!-- codex-research -->

# HTML/CSS Binary Caching Domain Research

## Relevant Prior Art

- Servo WebRender is a GPU-based renderer for web content. Its scene-building stage converts serialized display lists into renderer-suitable scenes, builds primitive lists, creates pictures for cached/filter content, stitches referenced display lists, and interns retained state between display lists. Sources: https://doc.servo.org/webrender/ and https://doc.servo.org/webrender/scene_building/index.html
- Chromium BlinkNG emphasizes containment and cached intermediate rendering data to avoid repeated computation. It identifies paint invalidation and display-list rasterization as expensive paths and uses containment principles to limit tree walks. Source: https://developer.chrome.com/docs/chromium/blinkng
- CSS containment/content-visibility lets an engine treat subtrees as isolated and skip style/layout/paint for offscreen or unnecessary content until needed. Source: https://web.dev/articles/content-visibility
- Flutter separates UI-thread scene/layer-tree construction from raster-thread GPU work. Its performance guidance warns that easy-to-build scenes can still be expensive to rasterize, and recommends retained/raster boundaries for static scenes while watching GPU memory. Source: https://docs.flutter.dev/perf/ui-performance
- Skia provides a common 2D API across software and hardware platforms and supports Vulkan as a selectable GPU backend. This supports a backend-abstracted renderer surface, but also shows that backend integration and driver variance are non-trivial. Sources: https://skia.org/docs/ and https://skia.org/docs/user/special/vulkan/
- Islands architecture keeps most UI static and loads/hydrates only interactive components. Islands can load in parallel and hydrate independently. Source: https://docs.astro.build/en/concepts/islands/
- List virtualization/windowing renders only visible items plus a moving window, recycling offscreen nodes. This is a different optimization from lazy loading and should become a renderer primitive for logs/tables/trees/editors. Source: https://web.dev/articles/virtualize-long-lists-react-window

## Techniques Beyond The Initial Proposal

1. Retained display lists and scene interning. Compile HTML/CSS/static Simple UI into stable primitive streams; intern unchanged primitives, styles, clips, and stacking contexts.
2. Dirty-region incremental style/layout/paint. Propagate dirty bits through explicit dependency edges and recompute only affected subtrees.
3. Containment boundaries. Add Simple UI annotations equivalent to layout/style/paint containment so pane-local changes cannot trigger whole-window work.
4. Viewport virtualization. Make lists, logs, trees, tables, editor lines, and repeated panes render through a visible-window primitive with overscan.
5. Text shaping and glyph caches. Cache shaped runs, font metrics, paragraph layout, glyph atlas pages, and fallback-font resolution by text/style/font tuple.
6. Layer promotion and compositing. Promote stable panes or animated transforms/opacities to retained layers/textures with damage tracking.
7. Compiler-assisted memoization. Use purity/input analysis to cache component render fragments and skip re-render when structural inputs are unchanged.
8. Data-oriented UI tree storage. Store nodes, properties, styles, event bindings, and layout boxes in arenas or struct-of-arrays with compact handles for traversal and binary serialization.
9. Pipeline/state caching for GPU backends. Cache shaders, pipelines, bind layouts, font atlases, and command templates to reduce first-frame jank.
10. Specialized 2D command buffer. Use a small backend-neutral command IR for fills, strokes, images, text, clips, transforms, and retained layers; lower to CPU, Vulkan, Metal, CUDA where practical.
11. Build/link size controls. Use feature-gated renderer backends, dependency-closure audits, LTO/dead stripping, profile-guided hot/cold splitting, and separate debug/devtools bundles.

## GPU/FPGA Offload Assessment

GPU offload is best for rasterization, compositing, image filters, transforms, large vector batches, glyph atlas drawing, and data-parallel layout for constrained layout models. It is weak for irregular DOM/CSS cascade, dynamic event logic, pointer/input dispatch, accessibility semantics, I/O, and arbitrary component control flow.

CUDA, Vulkan, and Metal should be treated as backend targets behind a common 2D/render command IR. Vulkan/Metal are plausible presentation and raster backends. CUDA can accelerate compute-heavy filters or specialized layout, but it is not a portable window/presentation layer. A pure Simple backend could generate shader/kernel artifacts for multiple targets, but the first requirement should be a portable IR and CPU reference backend; GPU binary generation should be a later backend capability with strict parity tests.

The Simple loop-limited mode for FPGA/GPU is promising only where algorithms are already bounded and data-parallel. General GUI logic should be partitioned into static/pure kernels and dynamic CPU orchestration rather than trying to eliminate all CPU interaction.
