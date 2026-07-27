# WM Glass QEMU Evidence Contract P1 Gaps — TLDR

- Status: open and fail-closed; neither QEMU row is a PASS.
- x86 still needs a published frozen manifest with no external-ELF bypass,
  SSE2/scalar parity, ordered damage/frame receipts, timing, and RSS.
- ARM direct-`-kernel` firmware is N/A; it still needs theme/material/backend/
  fallback identity and a receipt finalized after the correlated WM frame.
- Active sibling deltas are useful but remain uncommitted and partly
  synthetic; do not absorb them.
- A three-cycle isolated repair stopped at macOS `/dev/fd/7` executable
  permission denial; rejected/uncommitted candidates are not evidence.
- No fourth attempt, live QEMU, bootstrap, integration, or push ran.
- Resume frozen admission only after a reviewed descriptor-exec helper and raw
  immutable x86 ESP-image builder exist.
- Resume only with admitted source-matched artifacts through the canonical
  x86 and ARM evidence wrappers.

```sdn
wm_glass_qemu:
  committed_source -> frozen_admission -> ordered_events -> frame_capture
  missing_any_gate -> fail_closed
```
