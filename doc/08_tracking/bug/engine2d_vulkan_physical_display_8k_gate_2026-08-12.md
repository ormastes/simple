# Engine2D Vulkan physical-display 8K gate

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

Source readiness update (2026-08-14): the container campaign now builds and
retains a native `strict_semantic_vulkan_window_producer`. It lowers the same
changing Web semantics as A5, carries one Engine2D owner through strict submit
and visible-window presentation, and emits an explicitly presentation-only
receipt with zero timed readback. The physical wrapper runs that cached native
artifact after EDID/mode admission and validates an independent physical receipt
against the exact A5 run through the parent checker. The remaining open state is
hardware execution and captured/read-back scanout, not missing render source.

The canonical wrapper now has a fail-closed physical admission mode:
`DISPLAY=:0 ENGINE2D_VULKAN_PHYSICAL=1 sh
scripts/check/check-engine2d-vulkan-window-8k.shs`.  Unlike its default Xvfb
lane, physical mode requires an EDID-bearing connected X11 output with an
already-active 7680x4320 mode at 80 Hz or faster and validates the p95, RSS,
checksum, completion, fallback, adapter, and timed-readback receipt fields.
The EDID correlation rejects an externally managed Xvfb display instead of
trusting only its synthetic mode.  This closes the evidence-wrapper ambiguity;
it does not close the hardware blocker.

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

The 2026-08-14 host inventory has one connected HDMI connector whose advertised
modes top out at 1920x1080; the NVIDIA DisplayPort connectors are disconnected.
The physical wrapper therefore correctly reports a blocked admission on this
host.  Do not synthesize an 8K Xvfb mode to bypass this condition.

The same revision's one allowed proxy regression completed on the RTX A6000
with IMMEDIATE presentation, `readback_bytes=0`, known completion, no fallback,
checksum `14177648258271307651`, and max RSS 486812 KiB.  Its 20-frame p50/p95
were 185865702/193681044 ns.  This confirms the wrapper still functions after
physical-mode hardening and independently confirms that Xvfb is far outside
the 12.5 ms budget; it is not a physical-display result.
