<!-- codex-research -->

# HTML/CSS Binary Caching Feature Options

## Option A: Binary Static UI Cache At Shared Web Render Boundary

Description: Add a persistent binary cache for static HTML/CSS/Simple UI artifacts at the `WebRenderRequest`/`WebRenderArtifact` boundary. Cache parsed DOM/style/layout/display-list fragments for static panes while dynamic pane contents continue through patch/update paths.

Pros:
- Closest fit to existing shared renderer architecture.
- Lowers startup and repeated render cost without requiring a new GPU backend.
- Clear invalidation inputs: source, dependency graph, theme/CSS, viewport, fonts/assets, renderer/backend version, compiler/runtime version.
- Works for `ui.web`, Electron/Tauri-style hosts, and SimpleOS compositor through one contract.

Cons:
- Limited gains for highly dynamic panes unless combined with dirty-region updates.
- Requires a stable binary schema and migration/version policy.
- Current renderer is partial, so cache must avoid freezing fixture/fallback behavior as production output.

Effort: M. Expected 6-10 files across shared API metadata, browser-engine cache encode/decode, cache store, invalidation tests, and render smoke tests.

## Option B: Retained Scene Graph With Dirty Regions And Containment

Description: Build a retained UI scene with explicit static/dynamic/contained subtree boundaries. Recompute style/layout/paint only for dirty dependency slices, and emit incremental display-list or pixel damage updates.

Pros:
- Larger long-term performance win than parse caching alone.
- Directly addresses pane-local updates, scroll-heavy views, and repeated UI trees.
- Establishes the right architecture for later CPU/GPU backends.

Cons:
- Higher risk because it changes renderer lifecycle and invalidation semantics.
- Needs careful correctness tests for stale layout/style bugs.
- Requires more design before implementation to avoid duplicating existing browser-engine paths.

Effort: L. Expected 12-20 files across browser engine, web render API, compositor adapter, tests, and benchmark fixtures.

## Option C: Component Bundle Loader With First-Screen Eager Load And Background Lazy Load

Description: Introduce dependency-tracked UI component bundles. First-screen components load eagerly; lower-priority panes load asynchronously in background or on visibility/interaction. Static bundles may be binary cached.

Pros:
- Directly targets binary size and startup dependency closure.
- Matches existing lazy-init docs and package/dependency graph capabilities.
- Can be phased without rewriting layout/render internals.

Cons:
- Improves load time more than frame/render time.
- Needs deterministic dev/test eager mode to catch missing dependencies.
- Adds scheduler and diagnostics requirements.

Effort: M-L. Expected 8-14 files across dependency tracking, component registry, scheduler, diagnostics, and tests.

## Option D: Backend-Neutral 2D Command IR With CPU Reference And GPU Backends

Description: Define a compact retained 2D command IR that can lower to CPU software renderer first, then Vulkan/Metal/CUDA-capable backends for raster/composite/filter kernels. GPU binaries are cacheable backend artifacts.

Pros:
- Clean path to pure Simple CPU/GPU backend variants.
- Enables command-buffer caching, flyweight primitives, and backend-specific pipeline caches.
- Keeps GPU acceleration as an optimization behind a correctness-preserving CPU backend.

Cons:
- Does not by itself solve HTML/CSS parse or dependency loading.
- CUDA is not a portable GUI presentation backend, so backend scope must be precise.
- Significant parity, driver, and memory-budget verification required.

Effort: XL. Expected 20+ files and multiple phases across renderer IR, CPU backend, backend adapters, pipeline cache, parity tests, and benchmarks.

## Recommended Selection

Choose Option A + the containment/dirty-region subset of Option B for the first implementation. Treat Option C as a parallel follow-up for startup size. Keep Option D as an architecture track after the CPU reference cache is stable.
