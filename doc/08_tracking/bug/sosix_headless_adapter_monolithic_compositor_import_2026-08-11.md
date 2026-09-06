# SOSIX Headless Adapter Pulls Monolithic Compositor Closure

**Status:** fixed for the SOSIX adapter path; legacy compositor closure remains broad  
**Observed:** 2026-08-11

`src/os/compositor/host_services/headless_display_adapter.spl` must currently
import `HeadlessHostCompositorBackend` and its pixel accessor through
`os.compositor.host_compositor_entry`. The focused four-scenario integration
spec took about 20.7 seconds and compiled a broad renderer/GPU/library closure,
emitting many unrelated cross-family and duplicate-symbol warnings.

## Unblock design

Extract the headless framebuffer backend and its narrow `CompositorBackend`
implementation into a dedicated leaf module, preserve the existing façade by
re-export, and point the SOSIX adapter at that leaf. Acceptance requires the
same pixel oracle, no new renderer path, materially smaller dependency closure,
and measured cold/warm spec latency and maximum RSS.

## Resolution evidence

`HeadlessHostCompositorBackend` now lives in
`src/os/compositor/headless_host_backend.spl`. The historical compositor core
explicitly re-exports it, while the SOSIX adapter imports the leaf directly.
The same adapter spec remained 4/4 and its reported duration fell from about
20.7 seconds to 216 ms. The existing façade-based compositor occlusion spec
also remained 10/10, proving import compatibility, though its broad legacy
closure still took about 147 seconds and remains separate optimization work.
