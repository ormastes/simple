# Hosted WM source check exceeds 180 seconds

## Status

Open. Observed 2026-08-11 while verifying the existing-window Vulkan
submit-only path.

## Reproduction

```sh
SIMPLE_TIMEOUT_SECONDS=180 bin/simple check \
  src/os/compositor/compositor_engine2d.spl \
  src/os/compositor/host_compositor_core.spl \
  src/os/hosted/hosted_entry.spl
```

The self-hosted command remained CPU-bound and the watchdog terminated it at
180 seconds. It emitted no source diagnostic before termination. A narrower
60-second check of `hosted_entry.spl` behaved the same way.

## Impact

The focused source contract passes, and O3 optimizer analysis completes for
all three files, but the production Simple compile gate cannot currently be
completed within a practical verification bound. This blocks deployment and
live hosted-WM zero-readback timing; it must not be reported as an 8K/80 pass.

The same closure cost also prevents
`scripts/check/check-web-draw-ir-8k-frame-switch.shs` from reaching its first
render. Its wrapper formerly declared 180 seconds only to `timeout` while the
global CPU monitor killed it at 60 seconds; that propagation defect is fixed.
A subsequent bounded run reached the full 180-second limit without emitting an
evidence row, confirming that the remaining blocker is compilation rather than
the wrapper timeout mismatch.

## Acceptance

- The reproduction completes with a deterministic pass/fail diagnostic.
- Warm elapsed time and max RSS are recorded.
- The new hosted-WM Vulkan contract remains 3/3 green.
