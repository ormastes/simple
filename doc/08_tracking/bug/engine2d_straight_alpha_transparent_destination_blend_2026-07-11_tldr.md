# Transparent-Destination Blend — TLDR
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

```sdn
blend_bug:
  input: half_alpha_white_over_transparent
  current: 0x80808080
  expected_straight_alpha: 0x80FFFFFF
  impact: dark_antialiased_font_edges
```

Fix `color.blend` once, then refresh CPU/GPU parity anchors and add a transparent-destination oracle.

