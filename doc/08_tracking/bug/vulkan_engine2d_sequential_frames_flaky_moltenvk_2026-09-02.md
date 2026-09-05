# Vulkan Engine2D: sequential multi-frame runs flaky under interpreted MoltenVK

- **Filed:** 2026-09-02
- **Status:** PARTIALLY ROOT-CAUSED (2026-09-02, JIT lane) — the frame-2
  `completion_unknown` cascade is explained and fixed (see "Root cause"
  below). A separate intermittent SIGBUS under JIT+MoltenVK remains open
  (see "Still open").
- **Platform:** aarch64-apple-darwin, MoltenVK 1.4.350 (homebrew libvulkan),
  interpreted lane (Rust seed driver, `--features vulkan`)
- **Found during:** UI showcase feature-screen verification
  (`doc/05_design/ui_showcase_feature_screens.md`)

## Root cause (confirmed 2026-09-02, JIT lane)

The per-frame `engine.clear(RASTER_BG)` the GPU hosts issued before each
composition can fail its dispatch under MoltenVK; the failure sets
`VulkanBackend.completion_unknown = true` (backend_vulkan.spl `clear`: only
when `_dispatch_framebuffer_checked` returns < 0), and from then on every
draw op early-returns, so frame 2+ readbacks report `completion_unknown` /
"embedded-device-composite-not-proven". Reproduced deterministically: with
`engine.clear` per frame, frame 2 fails; without it, frame 2 passes with
`readback=device_readback` (59/0 then 60/0 rendered/skipped).

**Fix (shipped):** the Vulkan lanes no longer call `engine.clear` per frame.
Metal keeps its per-frame clear (stable there, and required: the glass theme
has no full-window opaque rect, so screen switches otherwise leave stale
pixels). The attempted alternative — injecting a full-window opaque ground
rect into the composition in `showcase_composition` — was REVERTED: both an
in-place `batches[0]` mutation and a prepend-batch rebuild intermittently
crashed the Metal JIT lane with heap corruption
(`___BUG_IN_CLIENT_OF_LIBMALLOC_POINTER_BEING_FREED_WAS_NOT_ALLOCATED` from
JIT code under lldb), while pristine sources passed 3/3. See
`jit_engine2d_static_create_silent_truncate_2026-09-02.md` for the JIT
miscompile family. Vulkan screen switches may show stale pixels until the
clear-dispatch failure itself is fixed.

## Still open

- Why `_dispatch_framebuffer_checked` returns < 0 for `clear` on frame 2+
  under MoltenVK (the poison trigger above; fence/wait path suspected).
- Intermittent `Bus error: 10` (SIGBUS) during frame 2 under the JIT lane
  with MoltenVK — no panic logged, dies right after a successful
  `[vk-order] flush rc=1`. Same binary+input passed in adjacent runs, so
  this retains the flaky classification. The earlier "device contention"
  speculation below is unchanged for this residue.

## What was observed (original report)

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

## Candidate directions (superseded for completion_unknown; kept for SIGBUS)

- ~~`VulkanBackend.completion_unknown` is set via
  `Engine2D._poison_vulkan_font_surface`~~ — confirmed, but the poison
  source was the per-frame `engine.clear` dispatch failure, not the font
  surface proof (see Root cause above).
- MoltenVK device contention (parallel interpreted vulkan processes + a live
  Metal GUI window were active during run 1) could plausibly make fence waits
  time out into the poison path. Nothing deterministic reproduces without
  that load, which is why this is filed as an observation, not a root cause.

## Related landed work from the same sweep

- `driver/Cargo.toml`: `vulkan = ["simple-compiler/vulkan"]` feature forward
  (the feature existed on compiler/runtime/native-all but was unreachable
  from the driver — same gap class as the 2026-09-01 `metal` forward).
- `vulkan/instance.rs`: the JIT lane's real `rt_vulkan_init` used
  `ash::Entry::load()`, which only dlopens the platform-default soname —
  Homebrew MoltenVK lives in `/opt/homebrew/lib`, off the dyld search path,
  so the JIT lane fell back where the interpreted lane (candidate-path
  probe) succeeded. Now probes the same candidate list.
- `common/src/runtime_symbols.rs`: 8 `rt_vulkan_*` entry points
  (`..._create_compute_pipeline_raw`, `..._present_buffer`, the three
  `..._init_*_present`, `..._accepted_compute_submit_count`, and both
  `..._provider_*`) were missing from `RUNTIME_SYMBOL_NAMES`, so release
  builds dead-stripped them and the interpreter's `dlsym(RTLD_DEFAULT)`
  dispatch could not find them.
- Showcase screens render all features on Vulkan: rects, alpha, bitmap and
  vector (TTF) text, polylines (PATH), scroll/clip groups, src-over blend.
