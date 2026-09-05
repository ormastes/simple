# check-engine2d-vulkan-window-8k passes via an xvfb device-present PROXY, not real window rendering

**Filed:** 2026-08-31
**Status:** OPEN
**Gate:** `scripts/check/check-engine2d-vulkan-window-8k.shs`

## What the gate actually proves

The gate runs the Rust unit test
`vulkan_graphics_runtime_swapchain::tests::bench_window_swapchain_present_8k_one_percent_damage`
under Xvfb and reports
`engine2d_vulkan_window_8k_evidence_status=pass scope=xvfb-device-present-proxy`.

The receipt itself is honest about the scope: the test exercises the
swapchain damage/present bookkeeping path on a real device (NVIDIA RTX A6000,
`readback_bytes=0`, `completion_known=true`, `present_mode=window-swapchain`),
but **no presented frame is ever captured or pixel-verified**. A regression
that presents garbage — or nothing — while keeping the bookkeeping consistent
would still pass. This is exactly the class of gap that kept the GUI window
gate (`check-gui-vulkan-window.shs`) red for weeks while this gate stayed
green: the same session (2026-08-31) found the deployed
`libsimple_runtime.so` built WITHOUT the vulkan feature and this gate did not
notice, because the Rust test rebuilds its own runtime.

## What real evidence would look like

The sibling gates already set the bar:
- `check-engine2d-vulkan-clear-8k.shs` — full-frame device readback compared
  against expectation (`engine2d_vulkan_evidence_readback_bytes=132710400`,
  `mismatch_count=0`).
- `check-gui-vulkan-window.shs` — offscreen PPM written from device readback
  plus a widget-content oracle (color count, ink coverage, edge clipping).

The window gate should either capture the Xvfb root after a present and
assert non-blank distinct content (the GUI gate's `window_distinct_colors`
approach), or read back the post-present swapchain image and checksum it
against the source damage buffer.

## Until strengthened

Treat `scope=xvfb-device-present-proxy` as NOT proving rendering. Rendering
claims for the window lane must cite `check-gui-vulkan-window.shs`
(`assert_vulkan_frame=pass`, `assert_widget_content=pass`) instead.
