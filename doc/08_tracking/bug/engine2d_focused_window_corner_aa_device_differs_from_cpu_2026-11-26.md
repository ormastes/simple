# Focused WM window corner AA differs from CPU by 1 LSB on the fresh device

- Status: open (P3), found 2026-11-26 on Linux aarch64, NVIDIA GB10 and
  llvmpipe, seed `cargo-target-wr-seed1126b`.
- Red handover spec: `test/02_integration/rendering/engine2d_focused_window_corner_device_spec.spl`.

A focused fluid_light window (10,36 120x80 in a 160x120 scene) composed by
`engine2d_draw_ir_adv_fresh_device_composition_with_images` differs from the
CPU composition at 20 pixels, bbox `10,36..129,115`: the rounded corners and
a few edge pixels, one LSB per channel (for example `(19,36)` device
`0xFFFCFBFE`, CPU `0xFFFBFAFE`). Same 20 pixels on both ICDs, and the same
before and after the retained-translucent change, so it is in the fresh
device path, not the damage replay. The unfocused window (opacity 930
group) matches exactly, which points at the focused (opaque, not grouped)
rounded window fill/border coverage rounding on the device.
