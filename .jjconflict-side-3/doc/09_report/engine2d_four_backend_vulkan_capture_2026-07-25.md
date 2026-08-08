# Engine2D Four-Backend Capture — Vulkan Lane

- status: **FAIL**
- revision under test: `d5a6312da1b6`
- target: macOS arm64 / MoltenVK
- requested capture: 3840x2160 at 300 DPI
- live gate: `scripts/check/check-macos-vulkan-2d-live-evidence.shs`
- live evidence: `build/tmp/engine2d-four-backend-vulkan/evidence.env`
- live report: `build/tmp/engine2d-four-backend-vulkan/report.md`

## Results

The Vulkan contract already requires device readback, a positive backend
handle, vector-font execution and cache receipts, six ordered target-side
focus/pointer/key events, pixel SHA-256, non-background bounds, and a durable
PPM/PNG. CPU mirrors and fallback sources are rejected.

The supplied pure-Simple native driver exits with code `4` before writing a
runtime receipt. The live gate therefore fails with
`launched-process-missing`; no framebuffer capture is accepted.

The current Vulkan provider itself is available: direct calls to
`rt_vulkan_provider_is_available` and `rt_vulkan_init` return `1`, device count
after initialization is `1`, and shutdown returns `1`. Provider initialization
is not the failing layer.

Rebuilding the harness from the current source is blocked by the required
self-hosted compiler. Running
`bin/release/aarch64-apple-darwin/simple check` on the Vulkan live harness exits
`1` with `semantic: array index out of bounds: index is 1 but length is 0`.
The existing native driver cannot replace fresh source-linked evidence.

## Verdict

`REQ-E2D4-002`, `REQ-E2D4-003`, and `REQ-E2D4-004` remain unproven for the
Vulkan lane. The honest result is FAIL; neither CPU fallback nor a stale native
binary is admitted as Vulkan capture evidence.
