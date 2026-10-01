<!-- codex-architecture -->
# Chromium Primitive Differential — TLDR

Test-only `libsimple_chromium_primitive_oracle` is a pinned Chromium C-ABI
bridge, dynamically loaded only from the no-GC test SFFI owner. It is not a
Chrome component ABI, a production renderer dependency, or a fallback.

Both Chromium and Simple convert their existing DOM/style/layout/paint/input/
GPU observations into the existing `NormalizedTrace`; Simple continues to use
private web state -> `DrawIrComposition` -> Engine2D. No WebIR/GuiIR or second
renderer exists. Primitive scope is rect/background/border, text metrics,
image, click/pointer/keyboard Ctrl+Alt, scroll/resize, optional linear path.

The adapter validates ABI v1 and five C symbols, uses caller-owned bounded JSON
buffers, opaque exact-once-released handles, rejects synthetic/malformed output,
and records a separate Simple Vulkan device-fence/readback/no-fallback receipt.
See [architecture](chromium_web_renderer_primitive_differential.md) and
[detail design](../05_design/chromium_web_renderer_primitive_differential.md).
