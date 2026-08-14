# Strict semantic Vulkan visible-window producer

This manual mirrors
`test/03_system/gui/wm_compare/strict_semantic_vulkan_window_producer_spec.spl`.

## Accepted device-window receipt

The producer lowers each changing Web semantic revision through canonical
DrawIR, submits it through strict Vulkan, and presents through the Engine2D
owner returned by that submission. A passing receipt requires one warmup,
sixty timed presentations, stable positive framebuffer/device/swapchain
identities, known completion, and no admitted fallback. The normal path requires
exactly 62 observed submissions and completed fences. A newly created swapchain
may require up to 16 explicitly counted, untimed history-seed presentations;
the receipt then requires exactly `62 + surface_seed_count` submissions and
completed fences. Any other fallback, or a seventeenth seed, fails closed.

The receipt explicitly binds `web-semantic-retained-damage-v1`, the
`simple-web-layout` and `engine2d-shared` owners, damage `(128,128,256,128)`,
and full-frame seeding before timing. The physical wrapper rejects any mismatch
against the correlated A5 producer receipt, including a stale workload,
geometry drift, or false independent-oracle parity.

## Timing and checksum boundary

The timed interval includes semantic lowering, strict submit/fence completion,
and visible swapchain presentation. It contains no host readback. Start/end
device readbacks are untimed and must produce distinct nonzero checksums.
The end checksum must equal A5's independently full-rendered strict Vulkan
oracle; the window receipt labels that authority rather than inventing a second
scanout oracle.

## Physical limitation

The receipt scope is `device-window-present-not-scanout-capture`. It can support
A6 source readiness but cannot promote A6 or A8. The physical operator must
still provide same-run EDID, connector, mode, and captured/read-back scanout
evidence. Unavailable window Vulkan exits 2; failed evidence exits 1.
