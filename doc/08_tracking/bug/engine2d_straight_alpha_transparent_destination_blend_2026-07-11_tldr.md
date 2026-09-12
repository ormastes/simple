# Transparent-Destination Blend — TLDR
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

```sdn
blend_bug:
  input: half_alpha_white_over_transparent
  current: 0x80808080
  expected_straight_alpha: 0x80FFFFFF
  impact: dark_antialiased_font_edges
```

Fix `color.blend` once, then refresh CPU/GPU parity anchors and add a transparent-destination oracle.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
