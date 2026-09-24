# TODO: [gpu][P2] Exercise the Metal provider probe on a host where metal_available() is true

Date: 2026-09-06
Lane: GPU scheduler hardening (plan doc/03_plan/ui/gpu_scheduler_hardening_gpu_resident_rendering.md)
Rule: this may not be closed by a source scan, a routing receipt, or an interpreter run.

Under the current seed the Metal probe reports unavailable (`rt_metal_is_available`
returns false) even on this Apple M4, while the same device answers through the
Vulkan/MoltenVK lane. The probe's available branch is therefore never executed here.

Closing evidence: a probe transcript from a host where `metal_available()` is true, showing a
non-empty device name and driver identity, and the conformance grade it produces.

## 2026-09-17 — probe exercised on the Apple M4 host (still open)

The probe was really executed on this Apple M4 host (not a source scan) via the seed
binary `bin/simple` (v1.0.1-beta.1 Mach-O seed, `SIMPLE_LIB=src`). Plain `test` and
`run` both work on this seed — no segfault, no `--mode=interpreter` fallback needed.

Commands run (worktree `build/mac-todo`, branch
`docs/macos-gpu-metal-probe-evidence-20260917`):

```
SIMPLE_LIB=src ./bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes_spec.spl
# -> 6 examples, 0 failures; SPEC FILE VERDICT outcome=OK; PASS (exit 0)

SIMPLE_GPU_TEST=1 SIMPLE_LIB=src ./bin/simple test test/03_system/app/ui.browser/feature/gpu_provider_conformance_device_spec.spl
# -> 2 examples, 0 failures, 2 skipped (Metal and DirectX gated scenarios skip cleanly);
#    Vulkan gated scenario passes; PASS (exit 0)

SIMPLE_LIB=src ./bin/simple run /tmp/metal_probe_driver.spl   # transcript driver, exit 0
```

Probe transcript (verbatim from the driver; Vulkan included because it reports the
same physical device the Metal branch would see):

```
provider=vulkan
api_level=vulkan-1.x
available=true
device_name=Apple M4
device_type=integrated
driver_identity=Apple M4|vendor=0000106b|device=1a040209|driver=000028a1|api=0040014e
distinct_phases=false
fence_token_available=false
device_timestamps_available=false
probe_error=
grade=routing_only
---
provider=metal
api_level=metal
available=false
device_name=
device_type=
driver_identity=
distinct_phases=false
fence_token_available=false
device_timestamps_available=false
probe_error=metal runtime not available on this host
grade=unavailable
---
provider=directx
api_level=d3d11-dxvk
available=false
device_name=
device_type=
driver_identity=
distinct_phases=false
fence_token_available=false
device_timestamps_available=false
probe_error=no D3D11/DXVK provider on macos
grade=unavailable
```

`metal_available()` is still false on the very host that owns the GPU, so per the
closing rule this row stays OPEN: no non-empty Metal device name or driver identity
was produced, and the available branch of `engine2d_gpu_probe_metal()` remains
unexercised. The Vulkan lane confirms the hardware is present and probed on this
machine (`device_name=Apple M4`, `driver_identity=...driver=000028a1...`).

Root cause is seed-side, not host hardware: the seed's Rust runtime has a real
`metal_impl` (calls `MTLCreateSystemDefaultDevice`) behind
`cfg(all(target_os = "macos", feature = "metal"))` in
`src/compiler_rust/runtime/src/metal_graphics_runtime.rs:929`, but the bootstrap seed
build compiles `simple-runtime` with only `--features runtime-symbol-table`
(`scripts/bootstrap/bootstrap-from-scratch.sh:2453`) — no `metal`. In the deployed
seed Mach-O, `rt_metal_init`, `rt_metal_is_available`, and `rt_metal_device_count`
all resolve to a single shared stub address (`nm bin/simple` → `00000001007bab9c`),
so every `rt_metal_*` probe answers 0. The portable C runtime is no better:
`rt_metal_is_available()` is a hardcoded 0 stub
(`src/runtime/runtime_core_host_services.c:94`, "The portable core capsule has no
Objective-C Metal provider"), and no Objective-C Metal provider exists anywhere in
`src/runtime/`. The dependent seams named by sibling rows stay extern-gated exactly
as written: no `addCompletedHandler`-backed phase extern, no
`rt_metal_command_buffer_event` / shared-event fence extern, no
`MTLCounterSampleBuffer` timestamp extern exists in this tree.

Unblock paths, either:
1. rebuild the macOS seed with the already-present `metal` cargo feature
   (`simple-runtime --features runtime-symbol-table,metal`) so `metal_impl` links,
   then re-run this transcript on any Apple-Silicon Mac; or
2. write an Objective-C Metal provider for the C runtime (new `src/runtime/*.m`,
   real `MTLCreateSystemDefaultDevice`) and run the transcript through a
   native-built binary.

Attribution: mac-todo lane, 2026-09-17, host Apple M4 (the only host that can
exercise this probe). Same shape as the DirectX precedent in PR #1037
(`doc/08_tracking/todo/gpu_directx_provider_probe_never_exercised_2026-09-06.md`):
row stays open with transcript + root cause recorded.
