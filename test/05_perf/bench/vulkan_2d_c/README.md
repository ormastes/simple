# Vulkan 2D benchmark: C reference vs Simple Engine2D

Apples-to-apples 2D workload over the same device (MoltenVK): per frame =
`vkCmdFillBuffer` clear + N rect-fill compute dispatches + submit + fence +
three-slot asynchronous submission ring. Optional full-frame capture happens
once after the timed samples and is excluded from p50/p95.

## Files

- `main.c` — the upstream example, fetched verbatim:
  `Magicalbat/videos` → `vulkan-compute/main.c` (426-line pure-C99 single-file
  headless Vulkan compute with `vkMapMemory` readback).
  <https://raw.githubusercontent.com/Magicalbat/videos/main/vulkan-compute/main.c>
- `vk2d_bench.c` — the 2D adaptation of that example: same instance/device/
  memory strategy (one HOST_VISIBLE|HOST_COHERENT allocation, first compute
  queue), plus a retained three-command-buffer/fence ring, five untimed
  warmups, nonblocking `vkGetFenceStatus` completion polling, per-frame
  draw/record-through-device-completion latency, deterministic teardown, and
  optional post-timing capture. Its receipt reports retained/released bytes,
  timed allocations,
  push-constant upload bytes, full-frame uploads, readbacks, completion polls,
  driver waits, event/frame generations, and damage area. Adds the
  `VK_KHR_portability_enumeration` flag MoltenVK requires.
- `rect.comp.glsl` — the rect-fill compute kernel (16×16 groups, push
  constants), compiled to `rect.spv`.
- `vk2d_bench.spl` — the Simple counterpart driving Engine2D's vulkan backend
  (`clear` + `draw_rect_filled` ×N + device-retained finalize). It performs no
  timed readback, captures once afterward when requested, and reports the
  current synchronous one-frame limitation as an inadmissible receipt. Missing
  backend telemetry is emitted as `-1` rather than inferred: timed allocation,
  retained/released bytes, upload bytes, and full-frame upload counts cannot be
  admitted until Engine2D exposes real counters.

## Build & run

```sh
glslangValidator -V rect.comp.glsl -o rect.spv
clang -std=c99 -O2 vk2d_bench.c -I/opt/homebrew/include -L/opt/homebrew/lib -lvulkan -o vk2d_bench
VK_ICD_FILENAMES=/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json ./vk2d_bench 800 600 64 300 0 5
# Arguments: width height rects samples capture_after_timing warmups
```

```sh
SIMPLE_LIB=src VK_ICD_FILENAMES=.../MoltenVK_icd.json \
  src/compiler_rust/target/vulkan/release/simple run test/05_perf/bench/vulkan_2d_c/vk2d_bench.spl
# knobs: VK2D_W VK2D_H VK2D_RECTS VK2D_FRAMES VK2D_WARMUPS VK2D_READBACK
```

## Comparison harness + gate

`sh scripts/check/check-vulkan-2d-c-compare.shs` builds/runs both legs and
writes `build/vulkan-2d-c-compare/evidence.env` (ratio vs budget, explicit
`skipped` rows when a toolchain leg is missing — never a fake pass).
It also retains the C producer streams as `c.stdout.raw` and `c.stderr.raw`;
on macOS the latter includes `/usr/bin/time -l` process statistics. The
canonical wrapper passes the committed `scenes.txt` as a required table and
rejects a C receipt unless it reports `scene_source=table`.
`c.runtime.env` binds those streams and maximum RSS, while `c.toolchain.env`
binds the C/shader compiler paths, hashes, versions, and exact flags.
The ratio is Simple p95 divided by C p95 with the selected 2.0x ceiling. Both
rows must already be `admitted`; raw measured output is intentionally reported
as `measured-unadmitted` until the common receipt validator accepts it. The live
path refuses Rust bootstrap-seed binaries.
The aggregate verdict logic is executable-tested by
`test/03_system/check/engine2d_vulkan_2d_perf_contract_spec.spl`.

Measured baseline + targets: `doc/02_requirements/nfr/engine2d_vulkan_2d_perf.md`.
