# Engine2D Vulkan physical-display 8K gate

Status: open

The same-device visible-window path reaches an NVIDIA RTX A6000 with
`IMMEDIATE` presentation, zero host readback, and no CPU fallback. Under Xvfb,
however, changed and retained 8K frames measure 78.768 ms and 70.120 ms p95.
The retained row skips the full framebuffer copy, so the remaining cost is the
physical-device-to-virtual-X-server presentation path.

This result cannot prove or disprove direct physical scanout throughput. Close
this gate only with an attached display/direct-display surface that records
7680x4320 viewport, device and driver identity, native present mode, p50/p95,
RSS/device memory, transfer/readback bytes, fallback and completion state, plus
a device-origin readback or captured scanout checksum. Cached retained replay
and changed-revision frames must be reported separately.
