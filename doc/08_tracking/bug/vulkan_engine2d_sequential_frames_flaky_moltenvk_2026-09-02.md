# Vulkan Engine2D: sequential multi-frame runs flaky under interpreted MoltenVK

- **Filed:** 2026-09-02
- **Status:** OPEN — observation, needs a deterministic local repro on a quiet
  machine before root-causing
- **Platform:** aarch64-apple-darwin, MoltenVK 1.4.350 (homebrew libvulkan),
  interpreted lane (Rust seed driver, `--features vulkan`)
- **Found during:** UI showcase feature-screen verification
  (`doc/05_design/ui_showcase_feature_screens.md`)

## What was observed

A driver rendering FIVE sequential showcase frames on one shared Engine2D
vulkan engine (clear + full composition + `engine2d_draw_ir_adv_composition_with_images`
per frame, distinct showcase trees per frame) produced two inconsistent outcomes
across runs in a busy environment:

- Run 1: frame 1 (overview) OK with `device_readback`; frames 2..5 reported
  `readback=completion_unknown` with `pixels=0` (and one frame —
  the scroll screen — fell back with 34 skipped text commands).
- Run 2 (same binary, quieter machine): no output for 25+ minutes.

Control runs, all passing with `readback=device_readback` and
`font_target=vulkan`:

- Each of the 5 screens in a FRESH process (5/5).
- Two sequential frames on ONE engine (overview → clear → fonts), including
  offscreen-child creation + composite per frame.
- Three consecutive offscreen composite cycles on one engine.

## Candidate directions (unproven)

- `VulkanBackend.completion_unknown` is set via
  `Engine2D._poison_vulkan_font_surface` when a font surface can't be proven
  on-device; once set, later readbacks fail closed. A frame-2+ font-surface
  proof failure would cascade exactly like the observed pattern.
- MoltenVK device contention (parallel interpreted vulkan processes + a live
  Metal GUI window were active during run 1) could plausibly make fence waits
  time out into the poison path. Nothing deterministic reproduces without
  that load, which is why this is filed as an observation, not a root cause.

## Related landed work from the same sweep

- `driver/Cargo.toml`: `vulkan = ["simple-compiler/vulkan"]` feature forward
  (the feature existed on compiler/runtime/native-all but was unreachable
  from the driver — same gap class as the 2026-09-01 `metal` forward).
- Showcase screens render all features on Vulkan: rects, alpha, bitmap and
  vector (TTF) text, polylines (PATH), scroll/clip groups, src-over blend.
