# WM Glass QEMU Evidence Contract P1 Gaps — TLDR

- Status: open and fail-closed; neither QEMU row is a PASS.
- x86 still needs a published frozen manifest with no external-ELF bypass,
  SSE2/scalar parity, ordered damage/frame receipts, timing, and RSS.
- ARM still needs firmware and theme/material/backend/fallback identity plus an
  event receipt finalized after the correlated WM frame.
- Active sibling deltas are useful but remain uncommitted and partly
  synthetic; do not absorb them.
- Resume only with admitted source-matched artifacts through the canonical
  x86 and ARM evidence wrappers.

```sdn
wm_glass_qemu:
  committed_source -> frozen_admission -> ordered_events -> frame_capture
  missing_any_gate -> fail_closed
```
