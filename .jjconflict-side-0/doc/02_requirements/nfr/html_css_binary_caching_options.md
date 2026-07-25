<!-- codex-research -->

# HTML/CSS Binary Caching NFR Options

## NFR Option 1: Conservative Cache And Size Gate

Description: Cache hit rendering must be measurably faster than cold parse/render on representative fixtures, with no more than a small startup RSS increase and no broad new startup dependencies.

Targets:
- Warm cache render latency: at least 30% faster than cold for static dashboard/browser fixtures.
- Startup RSS: no more than +5% versus current renderer on the same fixture set.
- Binary/cache schema overhead: documented and bounded per fixture.
- Verification: cache hit/miss metrics, invalidation tests, dependency-closure audit.

Pros:
- Low risk and suitable for first implementation.
- Forces explicit measurement without overfitting to GPU work.

Cons:
- May not satisfy aggressive frame-rate goals for dynamic panes.

Effort: M.

## NFR Option 2: Interactive Renderer Gate

Description: Add frame/update responsiveness targets for dynamic panes with containment, dirty regions, and async/background loading.

Targets:
- Pane-local update avoids full-window style/layout/paint for contained panes.
- First screen remains responsive while non-critical components load in background.
- Dynamic pane patch latency and frame-time p95 are measured on representative dashboard, table, tree, and editor fixtures.
- Deterministic eager-load mode exists for dev/test.

Pros:
- Directly supports responsive GUI behavior.
- Catches stale invalidation and scheduler regressions.

Cons:
- Requires more instrumentation and fixture work.

Effort: L.

## NFR Option 3: GPU Backend Readiness Gate

Description: Require backend-neutral CPU/GPU parity, resource ownership, and memory/driver fallback measurements before GPU offload is accepted.

Targets:
- CPU backend is the correctness oracle.
- GPU backend must pass pixel/parity tests for the same command IR.
- Pipeline/cache invalidation includes backend capability, shader/kernel version, renderer version, and driver/device identity where needed.
- Max GPU memory and CPU RSS are reported for promoted layers, glyph atlases, and command buffers.

Pros:
- Prevents premature CUDA/Vulkan/Metal coupling.
- Keeps pure Simple backend generation viable.

Cons:
- High setup and verification cost before visible wins.

Effort: XL.

## Recommended Selection

Select NFR Option 1 for the first cache milestone, and include the instrumentation hooks needed by Option 2. Select Option 3 only when GPU backend implementation starts.
