## 2026-09-16 re-verification (macOS sweep)

Command (macOS aarch64 M4 host):
`SIMPLE_GPU_TEST=1 SIMPLE_LIB=src build/cargo-r2/release/simple test test/03_system/app/ui.browser/feature/gpu_provider_conformance_device_spec.spl`
(binary `build/cargo-r2/release/simple`, 39,636,840 B, built 2026-09-14 with the cargo `metal` feature — links Metal.framework via objc2-metal)

Outcome: **FAIL — 2 examples, 1 failure** (exit 1). Verbatim:
```
Engine2D GPU provider conformance on this host
  ✗ probes every provider without a device and grades none of them full
    semantic: unknown extern function: rt_metal_device_identity
  ✓ unnamed

2 examples, 1 failure
SPEC FILE VERDICT: ... gpu_provider_conformance_device_spec.spl outcome=ERROR declared>=1 executed=2 passed=1 failed=1 skipped=0 dropped=0
```

What happened: the seed rebuilt 2026-09-14 DID fix the availability half of
this todo's premise — `rt_metal_is_available`/`rt_metal_create_device` now
answer a real device on this M4 (corroborated the same day by
`metal_msl_pipeline_spec` going 7/7 with real MSL pipeline compiles — see
`lane4_metal_and_vulkan_backend_specs_red_2026-09-12.md`). But the probe
transcript this todo demands still cannot be produced: the Metal probe calls
`rt_metal_device_identity` (extern at `src/lib/nogc_sync_mut/io/metal_sffi.spl:26`,
invoked from `metal_sffi_device_registry_identity` :410), and that extern is
**GENUINELY_MISSING from the seed** — it is not in the binary's runtime symbol
table (present Metal externs: `rt_metal_init/is_available/device_count/device_name/
device_memory/create_device/...`; `strings` finds no `rt_metal_device_identity`),
matching the GENUINELY_MISSING census entries in
`doc/08_tracking/bug/data/sffi_contract_inventory_2026-08-21.tsv` and
`unbacked_extern_census_2026-08-18.tsv`. `rt_metal_device_supports_metal3` is
likewise still missing. The semantic pass therefore kills the probe-all example
before any identity/grade transcript prints, and the gated Metal scenario does
not execute (its `metal_lane_ready()` predicate hits the same missing extern).
The Vulkan gated scenario is the passing example.

Resulting status: **OPEN** — no device transcript was produced, and this todo's
rule forbids closing without one. Fresh blocker to record: implement
`rt_metal_device_identity` (and `rt_metal_device_supports_metal3`) in the Rust
runtime, rebuild the seed, then re-run the same command — the transcript
(device name / registry identity / conformance grade) should then print.

# TODO: [gpu][P2] Exercise the Metal provider probe on a host where metal_available() is true

Status: OPEN (re-verified 2026-09-16: the 2026-09-14 Metal-featured seed makes the probe available, but the spec still cannot produce the identity transcript — `rt_metal_device_identity` remains GENUINELY_MISSING from the seed, so the probe-all example dies at semantic with "unknown extern function"; no transcript, still open per its rule — see "2026-09-16 re-verification (macOS sweep)" above)

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
