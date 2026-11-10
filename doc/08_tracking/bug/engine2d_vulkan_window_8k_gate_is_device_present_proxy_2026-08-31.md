# check-engine2d-vulkan-window-8k passes via an xvfb device-present PROXY, not real window rendering
## Open 2026-11-11 — re-verified LIVE by lane ne8 (see dated addendum at end)

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


---

## 2026-11-11 addendum — lane ne8 (P3 traverse, batch ne8)

**Verdict: LIVE — the default gate lane is still a device-present proxy with no pixel
verification. Kept OPEN.**

- `scripts/check/check-engine2d-vulkan-window-8k.shs` (release tip, last touched by PR #7597,
  2026-11-07) still runs only the Rust swapchain-bookkeeping test
  `bench_window_swapchain_present_8k_one_percent_damage` under Xvfb and, on the default lane,
  still emits exactly `engine2d_vulkan_window_8k_evidence_status=pass
  scope=xvfb-device-present-proxy`. Its header now states honestly that "the default disposable
  Xvfb lane is evidence collection, not an 8K/80 pass gate".
- The receipt assertions on the default lane remain bookkeeping-only
  (`readback_bytes=0`, `completion_known=true`, `present_mode=window-swapchain`,
  `device_type=...`); no presented frame is captured and no pixel/content oracle runs. A
  regression presenting garbage or nothing while keeping bookkeeping consistent would still
  pass — the doc's core finding stands.
- A PHYSICAL lane (`ENGINE2D_VULKAN_PHYSICAL=1`, added in the 2026-11-07 render hardening
  series) now requires a real EDID-verified 7680x4320@80 X11 mode and enforces p95 timing +
  non-zero checksum + RSS. That raises the bar for the hardware lane but (a) cannot run in CI
  or on this Windows lane (no Xvfb/NVIDIA ICD here), and (b) still does not compare presented
  pixels against an expectation — `checksum > 0` is presence, not correctness. The sibling
  pixel-verified gates (`check-engine2d-vulkan-clear-8k.shs` readback-compare,
  `check-gui-vulkan-window.shs` `window_distinct_colors` + widget oracle) remain the bar this
  gate does not meet.
- **Not fixed in this lane:** strengthening needs a Rust runtime change (frame capture /
  swapchain-image readback + checksum vs the source damage buffer in the
  `vulkan_graphics_runtime` test), which is outside a no-cargo interpreter-seed lane and
  un-runnable on this host. The "until strengthened" reporting rule below remains in force.
