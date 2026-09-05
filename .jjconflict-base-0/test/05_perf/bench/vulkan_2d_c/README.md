# Vulkan 2D benchmark: C reference vs Simple Engine2D

Apples-to-apples 2D workload over the same device (MoltenVK): per frame =
`vkCmdFillBuffer` clear + N rect-fill compute dispatches + submit + fence +
optional full-frame readback.

## Files

- `main.c` — the upstream example, fetched verbatim:
  `Magicalbat/videos` → `vulkan-compute/main.c` (426-line pure-C99 single-file
  headless Vulkan compute with `vkMapMemory` readback).
  <https://raw.githubusercontent.com/Magicalbat/videos/main/vulkan-compute/main.c>
- `vk2d_bench.c` — the 2D adaptation of that example: same instance/device/
  memory strategy (one HOST_VISIBLE|HOST_COHERENT allocation, first compute
  queue, one-shot command buffer per frame, one fence wait per frame), plus
  the 2D frame loop (clear + N rects + optional readback). Adds the
  `VK_KHR_portability_enumeration` flag MoltenVK requires.
- `rect.comp.glsl` — the rect-fill compute kernel (16×16 groups, push
  constants), compiled to `rect.spv`.
- `vk2d_bench.spl` — the Simple counterpart driving Engine2D's vulkan backend
  (`clear` + `draw_rect_filled` ×N + `submit_batch` + `present` +
  `read_pixels_with_source`) with per-phase timing (draw / submit / readback).

## Build & run

```sh
glslangValidator -V rect.comp.glsl -o rect.spv
clang -std=c99 -O2 vk2d_bench.c -I/opt/homebrew/include -L/opt/homebrew/lib -lvulkan -o vk2d_bench
VK_ICD_FILENAMES=/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json ./vk2d_bench 800 600 64 300 1
```

```sh
SIMPLE_LIB=src VK_ICD_FILENAMES=.../MoltenVK_icd.json \
  src/compiler_rust/target/vulkan/release/simple run test/05_perf/bench/vulkan_2d_c/vk2d_bench.spl
# knobs: VK2D_W VK2D_H VK2D_RECTS VK2D_FRAMES VK2D_READBACK
```

## Comparison harness + gate

`sh scripts/check/check-vulkan-2d-c-compare.shs` builds/runs both legs and
writes `build/vulkan-2d-c-compare/evidence.env` (ratio vs budget, explicit
`skipped` rows when a toolchain leg is missing — never a fake pass).
The aggregate verdict logic is executable-tested by
`test/03_system/check/engine2d_vulkan_2d_perf_contract_spec.spl`.

Measured baseline + targets: `doc/02_requirements/nfr/engine2d_vulkan_2d_perf.md`.
