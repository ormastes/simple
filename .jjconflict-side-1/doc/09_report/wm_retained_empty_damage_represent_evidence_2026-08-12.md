# WM Retained Empty-Damage Re-present Evidence — 2026-08-12

Status: **EXACT-KEY PASS / STRUCTURAL REPLAY SKIP / LIVE VULKAN UNPROVEN**

The WM damaged-window entry now checks its exact retained key before seed or
damage-list fallback only when the invalidation list is empty. When producer generation, composition revision, full
canonical `DrawIrComposition`, and immutable image resources all match, it
routes to the existing swapchain re-present path. An empty invalidation list no
longer causes a full DrawIR render and damage-plan build for an unchanged frame.

The exact-key behavioral spec passed. It covers matching and mismatched
generation, revision, composition, and resources; revisions alone are never
trusted. The retained route still requires a successful `window-swapchain`
receipt with completed device presentation, known completion, and no readback.
Changed, malformed, or nonempty-damage frames preserve the existing
full/damaged fallback rules even if a caller accidentally reuses a revision.

The source-routing spec could not provide evidence in this checkout: three
bounded seed-runner cycles failed 0/2 because both scenarios received empty
source text, including the untouched host-compositor scenario. No further retry
was made. This row therefore claims exact-key behavior plus reviewed structural
routing only, not a live Vulkan re-present or 8K/80 measurement.

The standalone checker was also unavailable: the bootstrap seed delegated to
`bin/simple`, which is intentionally absent from the isolated checkout. Its
exit 127 is not reported as source-check evidence.
