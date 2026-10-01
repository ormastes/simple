# First Simple-vs-C Vulkan 2D measurement on Linux (2026-09-06)

Host: NVIDIA GB10, Vulkan 1.4.312, ICDs `/usr/share/vulkan/icd.d/{nvidia,lvp}_icd.json`.
Seed: `src/compiler_rust/target/vulkan/release/simple` built with `--features vulkan`
from `origin/main` @ `63924350c16`. Workload w=800 h=600 rects=64 frames=300,
shared scene table `test/05_perf/bench/vulkan_2d_c/scenes.txt`, readback on.

## Raw lines (`sh scripts/check/check-vulkan-2d-c-compare.shs`, two runs)

    c_line=c-vulkan-2d w=800 h=600 rects=64 frames=300 readback=1 ms=44.3 fps=6774.8 checksum=10505124
    simple_line=simple-vulkan-2d w=800 h=600 rects=64 frames=300 readback=true ms=3034 fps~=98 draw_us=557287 batch_us=676699 present_us=824369 readback_us=976384 checksum=10460147 frame_mismatches=0
    compare_budget_x1000=100
    compare_ratio_x1000=14
    compare_status=fail
    compare_reason=below-budget:14<100

    c_line=c-vulkan-2d w=800 h=600 rects=64 frames=300 readback=1 ms=32.3 fps=9279.5 checksum=6558172
    simple_line=simple-vulkan-2d w=800 h=600 rects=64 frames=300 readback=true ms=2195 fps~=136 draw_us=570098 batch_us=670862 present_us=829508 readback_us=124530 checksum=10460147 frame_mismatches=0
    compare_budget_x1000=100
    compare_ratio_x1000=14
    compare_status=fail
    compare_reason=below-budget:14<100

## Result

C is **~69x faster**: within run 1 the ratio is 6774.8/98 = 69x, within run 2 it is
9279.5/136 = 68x, and `compare_ratio_x1000=14` in both. Simple reaches 1.4% of
the C leg. (Do not pair fps figures across runs — the C leg varies run to run.)
Per Simple frame (run 2): draw 1900us, submit_batch 2236us, present 2765us,
readback 415us = ~7.3ms. The C leg does the whole frame in ~108us. The cost is
spread evenly across draw/batch/present, which is the shape of per-op
interpreted marshalling, not GPU time.

## The `VK_KHR_surface` lead was FALSE

The reported blocker (`status=blocked reason=backend-unavailable`, attributed to
a missing `VK_KHR_surface`) does not reproduce. `vulkaninfo --summary` lists 21
instance extensions **including `VK_KHR_surface` revision 25** and
`VK_EXT_headless_surface`. Direct probe of the Simple lane on this host:

    VulkanSession.init() -> code=0, init_error="", is_valid()=true
    VulkanBackend.create().init(800,600) -> true, last_error=""

The lane demanded nothing spurious and needed no change. The earlier
`backend-unavailable` is best explained by a seed built BEFORE the already-landed
`src/compiler_rust/runtime/src/vulkan/instance.rs` fix that gates the
platform-specific surface extensions (`VK_KHR_xlib_surface` /
`VK_KHR_wayland_surface`, both genuinely absent here) on loader availability.
That fix's own comment describes the parent's exact symptom (`rt_vulkan_init -> 0`),
and a seed rebuilt with it initializes first try. This is inference from strong
evidence, not something verified against the parent's actual binary.

## Two open observations (not fixed here)

1. `check-vulkan-2d-c-compare.shs` prints `compare_status=fail` but **exits 0**;
   its own header says exit 1 when both legs ran below budget.
2. The C leg's checksum is NOT stable across runs (10505124, then 6558172) while
   the Simple leg's is (10460147, frame_mismatches=0). The two legs also disagree
   with each other. A pixel-parity claim between the legs is not yet supportable.

## Execution site: BOTH legs ran on the same real GPU (verified)

This host enumerates two Vulkan physical devices, and the order matters because
`lvp_icd.json` sorts before `nvidia_icd.json` in `/usr/share/vulkan/icd.d/`.
It does not decide the outcome here — `vulkaninfo --summary` reports:

    GPU0: deviceName = NVIDIA GB10, deviceType = PHYSICAL_DEVICE_TYPE_INTEGRATED_GPU, driverName = NVIDIA
    GPU1: deviceName = llvmpipe (LLVM 20.1.2, 128 bits), deviceType = PHYSICAL_DEVICE_TYPE_CPU, driverName = llvmpipe

Index 0 is the NVIDIA GB10, not the software rasterizer.

- Simple leg: `VulkanSession.init()` calls `vulkan_sffi_select_device(0)`
  (`src/lib/gc_async_mut/gpu/engine2d/vulkan_session.spl:196`) -> GB10.
- C leg: `vk2d_bench.c:76-77` sets `u32 n = 1` and takes the single device
  `vkEnumeratePhysicalDevices` writes back, i.e. index 0 -> GB10. It prints a
  `device: <name>` line, which the compare gate filters out because it greps
  only `^c-vulkan-2d`.

So the ratio is a language/runtime comparison on identical hardware, and the
"cost is interpreted marshalling, not GPU time" reading stands.

## JIT status of the Simple leg

The bench run was grepped for `jit` and emitted no `[jit-fallback]` line, so the
bench module was JIT-compiled, not dropped to the interpreter. (A throwaway
probe module in the same session DID emit
`[jit-fallback] ... whole module dropped to the interpreter`, for an unrelated
HIR field-inference limit — that message is what the absence here is measured
against.) This matters because the interpreter's own advertised penalty is
~100-1000x, which brackets the 69x gap; the gap is NOT explained by the bench
falling off the JIT.
