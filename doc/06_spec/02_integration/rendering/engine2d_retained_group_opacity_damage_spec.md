# Engine2D Retained Damage Replay of Unfocused Window (Opacity 930) Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 2 | 2 | 0 | 0 |

## Overview

Verifies `REQ-S2D-002`, `REQ-S2D-003`, and `NFR-S2D-001`: retained damage replay of
an unfocused WM window (`opacity_milli == 930`) under a partial damage clip
crossing the window boundary produces pixel-identical output to split full frames
inside and outside the damage region on both CPU and Vulkan.

## Scenarios

### Fluid Light unfocused window content change under partial damage clip

1. Seed CPU and Vulkan targets with frame A (`fluid_light` theme, unfocused window at `(10, 36)`).
2. Replay frame B (updated content image) under damage rect `[0, 40, 60, 40]`.
   - Expected: `unsupported_kinds == "none"`, device composite succeeds with `readback_source == "device_readback"`, and pixels equal frame B inside the damage and frame A outside.

### Aetheric Dark unfocused window content change under partial damage clip

1. Repeat with `aetheric_dark_theme_render_snapshot()`.
   - Expected: exact CPU and Vulkan device parity inside and outside the damage clip.

## Source

- Executable spec: `test/02_integration/rendering/engine2d_retained_group_opacity_damage_spec.spl`
- Tracked bug: `doc/08_tracking/bug/engine2d_retained_damage_rejects_unfocused_window_opacity_2026-11-26.md`
