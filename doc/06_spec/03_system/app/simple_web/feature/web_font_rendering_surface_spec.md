# Simple Web Font Rendering Surface

> **Status: BLOCKED.** The pure-Simple focused SSpec currently stops with
> `runtime error: field access on nil receiver` before it can emit the
> authoritative production composition receipt. Browser-only evidence is not a
> substitute and cannot pass this manual.

| Tests | Passing | Blocked | Stubs |
|-------|---------|---------|-------|
| 2 | 0 | 2 | 0 |

## Claim boundary

This manual covers production Simple HTML/WebIR text lowering into the exact
submitted `DrawIrComposition`, its Engine2D pixel artifact, and a later live
Electron event/frame receipt tied to that authoritative artifact. It does not
claim Vulkan, hosted-WM, GUI-widget, or SimpleOS QEMU completion.

Source:
`test/03_system/app/simple_web/feature/web_font_rendering_surface_spec.spl`

## Required flow

1. **Trace the production font and event boundary**
   - Follow HTML through WebIR into the exact `DrawIrComposition`, then the
     shared Engine2D pixel facade; WebIR is not a second drawing IR.
2. **Load the pinned multilingual font manifest**
   - Resolve the exact Noto Sans Mono manifest identity:
     `sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081;axes=wght=400,wdth=100`.
3. **Accept exact-face-bound simple-script shaping**
   - Require one `WEB` text command with three ordered positive advances.
4. **Build the production surface composition**
   - Use the production HTML/WebIR owner; do not synthesize Draw IR.
5. **Prepare one shared font batch for 2D and 3D**
   - Keep font material transient behind the shared Engine2D executor.
6. **Emit the selected font composite program and plan compilation**
   - Submit the same composition object to the shared pixel facade.
7. **Submit the boundary output to its canonical consumer**
   - Compare each ordered glyph band against the otherwise identical blank
     frame.
8. **Prove native submission and device readback**
   - Retain the 96×48 ARGB artifact and write its exact pixel count, weighted
     checksum, file size, SHA-256, and caller-supplied run ID into
     `build/test-artifacts/simple-web-font-composition/receipt.env`.
9. **Deliver correlated focus keyboard and pointer events**
   - The browser wrapper must consume that receipt and artifact before launch.
     It must fail when the run ID is omitted or differs from the receipt, or
     when either artifact is missing, malformed, or mismatched.
10. **Correlate visible pixels and input with one frame identity**
   - Retain a post-interaction `WEB` glyph crop. Its correlation ID includes
     the caller run ID, authoritative Simple composition checksum, and event
     count.
11. **Reject disconnected stale or replayed evidence**
    - Re-run the wrapper unchanged with a deliberately stale caller run ID and
      then with the same run ID and unchanged receipt. Both runs must exit
      nonzero with, respectively, `simple-web-font-run-id-mismatch`
      and `simple-web-font-run-id-replayed`. The scenario does not rewrite or
      self-stamp a receipt to make a replay appear fresh.

Freshness is fail-closed only when both stale and same-ID replay probes reject.
After a PASS, the wrapper atomically creates a receipt-adjacent consumed-run
guard. Concurrent probes may execute, but only one can claim final PASS for a
receipt/run ID. The receipt does not currently bind a self-hosted binary hash,
so this manual does not claim cryptographic source/binary provenance.

## Current blocker

Run:

```sh
SIMPLE_WEB_FONT_RUN_ID="web-font-$(date -u +%Y%m%dT%H%M%SZ)-$$"
export SIMPLE_WEB_FONT_RUN_ID
SIMPLE_LIB=src bin/simple test test/03_system/app/simple_web/feature/web_font_rendering_surface_spec.spl --mode=interpreter
```

Current result: BLOCKED before the receipt is written. Therefore
with a fresh run ID, `scripts/check/check-wm-browser-event-routing-evidence.shs`
must report `missing-simple-web-font-composition-receipt` (and must report
`missing-simple-web-font-run-id` when invoked without one), and
`scripts/check/check-production-gui-web-renderer-parity-evidence.shs` must not
promote Web font/event PASS.

The checker rejects a stale caller run ID and an unchanged same-ID receipt.
This source change remains runtime-unverified until the pure-Simple runner can
create the first authoritative receipt.

Earlier browser-only artifacts were moved non-destructively under
`build/rejected-evidence/`; they are diagnostic evidence only.

## Resume

After the shared Engine2D construction invariant is repaired, run the focused
SSpec once in a fresh verification session. A passing first scenario creates
the authoritative receipt; only then may the second scenario launch the live
browser wrapper. Regenerate this manual with `spipe-docgen` after that run.
