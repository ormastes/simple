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
- Darwin has no reviewed `fexecve`; resume only after a supervised,
  provenance-bound `posix_spawn`/fdset helper and raw immutable ESP builder.
- The helper can claim honest same-UID race resistance only; malicious same-UID
  admission stays unavailable without a privileged OS-immutable store.
- Helper candidate `e98275fca0` hit its three-cycle cap with supervision,
  closure admission, wrapper wiring, raw-profile isolation, and behavior tests
  still missing; it is unintegrated and not evidence.
- It also lacks truthful exact helper-build provenance and pre-spawn
  validation/receipt reservation with no-orphan kill-and-wait cleanup.
- BRR2 source cycles `a2e949d838`/`2edbe367ed`/`c10eff40a9` also hit the
  three-cycle cap and remain unintegrated: public capture collapses exact parser
  failures, while selected requirements/design still misapply the legacy
  six-event contract to the distinct SimpleOS four-stage lifecycle.
- Resume only with admitted source-matched artifacts through the canonical
  x86 and ARM evidence wrappers.

```sdn
wm_glass_qemu:
  committed_source -> frozen_admission -> ordered_events -> frame_capture
  missing_any_gate -> fail_closed
```
