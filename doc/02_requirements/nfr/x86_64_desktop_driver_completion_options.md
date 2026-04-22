<!-- codex-research -->
# NFR Options: x86_64 Desktop Driver Completion

## Option 1: Deterministic QEMU Acceptance

Description: Driver completion is accepted only by bounded QEMU runs with deterministic serial markers and no resident fallback markers.

Pros:
- CI-friendly.
- Clear pass/fail surface.
- Matches current SimpleOS verification style.

Cons:
- Does not measure real hardware variability.

Effort: M.

## Option 2: Safety And Truthful Capability Reporting

Description: Option 1 plus required capability summaries for DMA, interrupt mode, polling fallback, acceleration state, and unsupported advanced features.

Pros:
- Prevents false claims such as VGA DMA or hidden zero-copy.
- Helps debug driver regressions.
- Aligns with existing driver DMA and display NFRs.

Cons:
- Requires small reporting APIs across driver families.

Effort: L.

## Option 3: Performance-Gated Driver Completion

Description: Option 2 plus latency/RSS/throughput gates for disk read, framebuffer update, packet send/recv, and boot-time device discovery.

Pros:
- Prevents slow “complete” drivers from becoming the baseline.
- Useful before release-quality desktop claims.

Cons:
- More brittle until the QEMU lane is stable.
- Requires benchmark fixture maintenance.

Effort: XL.

## Recommendation

Option 2 is the best default. Use deterministic QEMU markers and truthful capability reporting first; add performance gates once the driver matrix is passing.

