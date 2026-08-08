<!-- codex-research -->
# Chromium Web Renderer Primitive Differential — Domain Research

Chromium's RenderingNG documentation identifies animate, style, layout,
pre-paint, scroll, paint, commit, layerization, raster, activation,
aggregation, and GPU draw as distinct operations. It also describes input
routing and scrolling as part of the rendering pipeline. The adapter therefore
compares a deliberately small semantic projection at DOM/style/layout/paint/
input/GPU boundaries rather than Chromium display-list bytes or internal object
addresses. [RenderingNG architecture](https://developer.chrome.com/docs/chromium/renderingng-architecture)

The Chromium component-build guide says component exported symbols are not the
public API and highlights load-time/duplication risks for excessive component
granularity. The integration must consequently build one owned, test-only
bridge with a narrow C ABI; it must not discover or bind private Blink/Viz
components dynamically. [Chrome Component Build](https://chromium.googlesource.com/chromium/src/%2B/master/docs/component_build.md)

Chrome DevTools Protocol exposes synthetic mouse and keyboard dispatch, which
is useful to drive the fixture but does not by itself produce trustworthy
cross-engine semantic output. The bridge records post-dispatch target/default
action facts and framebuffer/device-receipt facts, all normalized before
comparison. [CDP Input domain](https://chromedevtools.github.io/devtools-protocol/1-2/Input/)

The design avoids a claim that Chrome GPU raster proves Simple Vulkan execution:
each renderer has its own GPU receipt. Simple promotion still requires a
Vulkan device fence and device-origin readback under the existing environment
profile; Chrome is an independent layout/paint reference, not a production
backend or a substitute for that receipt.
