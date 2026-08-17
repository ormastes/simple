# Transparent-Destination Blend — TLDR

Status: DUPLICATE of engine2d_native_blend_diverges_from_scalar_on_varied_patterns_2026-08-15.md
Status re-verified 2026-08-17 by source inspection (triage shard 01).

```sdn
blend_bug:
  input: half_alpha_white_over_transparent
  current: 0x80808080
  expected_straight_alpha: 0x80FFFFFF
  impact: dark_antialiased_font_edges
```

Fix `color.blend` once, then refresh CPU/GPU parity anchors and add a transparent-destination oracle.
