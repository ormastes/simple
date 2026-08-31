# In-guest Vulkan does not exist in SimpleOS; every WM smoke frame is CPU-rendered

Date: 2026-08-31
Scope: goal item 2 — x86_64 / arm64 / riscv64 SimpleOS window-manager smoke tests
with a "Vulkan-backed 2D path".

## Verdict

**There is no in-guest Vulkan path.** Any SimpleOS window-manager frame captured
today — on any of the three architectures — is **CPU-rendered**. Labelling such a
frame "Vulkan-backed" would be false.

What exists instead is a *third* thing, neither in-guest Vulkan nor plain CPU: a
**guest -> host ivshmem offload** with a genuine host-side Vulkan daemon. It is
real, but it does not render the window manager and it does not boot under real
firmware. Details below.

## Evidence (three independent confirmations)

1. **The compositor's Vulkan backend rejects all drawing by contract.**
   `src/os/compositor/backend_factory.spl:77-83` registers `ScreenType.Vulkan` ->
   `VulkanCompositorBackend`, and its own comment states
   `VulkanCompositorBackend.is_available()` is unconditionally false. The backend
   file (`src/os/compositor/vulkan_compositor_backend.spl:12`) carries an explicit
   honesty contract: *"No method here talks to a GPU, a venus ring, or any Vulkan
   API."* Its only real probe is `is_char_device(render_node)` — a stat(2)
   `S_ISCHR` test that any character device (e.g. `/dev/null`) passes, and which
   the file itself says callers "must not read as 'Vulkan works'". Drawing remains
   rejected regardless of the probe result.

2. **Every `rt_vulkan_*` entry point is compiled out inside the guest.**
   `examples/09_embedded/simple_os/arch/x86_64/boot/freestanding_optional_backends.c:120-132`:
   *"Host Vulkan SFFI is unavailable inside SimpleOS. The guest's framebuffer path
   remains authoritative; any accidental host-Vulkan operation fails."* Twelve
   `rt_vulkan_*` symbols are defined as `UNAVAILABLE(...)` / `ABSENT(...)` stubs.
   This is a link-level guarantee, not a runtime policy.

3. **The baremetal 2D engine has zero Vulkan references.**
   `src/os/compositor/engine2d_baremetal_core.spl` — the in-guest rasteriser —
   contains no Vulkan symbol of any kind. Real Vulkan under `src/os/` lives only in
   host/board ports (`src/os/port/qrb2210_*vulkan*`, `src/os/hosted/hosted_entry.spl`)
   and in the host-offload adapter (`src/os/lib/gpu_bridge/vulkan_host_offload_adapter.spl`).

## The host-offload path: real Vulkan, wrong shape

`scripts/check/check-simpleos-qemu-host-gpu-2d.shs` (3231 lines) is *not* a
fail-open proxy. It links the host runtime with the `vulkan` cargo feature,
requires the `rt_vulkan_provider_is_available` / `rt_vulkan_init` /
`rt_vulkan_compile_spirv_raw` / `rt_vulkan_create_compute_pipeline` symbols to be
present, runs `src/app/simpleos_gpu_host/` as a daemon, and asserts a
`HOST_GPU_PROCESS_OK isa=<isa> backend=vulkan` receipt plus a 1280x720 pixel
checksum (`HOST_GPU_FIXTURE_CHECKSUM=1417723768`, 633600 background + 288000 rect
pixels). That is genuine GPU rendering with pixel assertions.

Two reasons it does not satisfy this goal:

- **It is not the window manager.** It renders a 2D fixture through
  `host_gpu_ivshmem_probe_entry.spl`, not a WM frame. (The WM frame executor *does*
  support the path — `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl:598`
  calls `Engine2dWmFrameExecutor.create_host_gpu(..., SIMPLEOS_HOST_GPU_BACKEND_VULKAN, ...)`
  — so wiring the WM to it is plausible future work, not a rebuild.)
- **It boots the guest with `-kernel -nographic`, violating `.claude/rules/board-runnable.md`.**
  This is not incidental: the gate's own argv validator *requires* `-kernel` at a
  fixed argv position (lines 1306, 1334, 1350, 1366, 1377), so `-kernel` is the
  encoded contract of the lane, not a stray fixture. Migrating it onto OVMF/EDK2/OpenSBI
  is a separate, sizeable piece of work.

`check-rv64-display-smoke-qmp-evidence.shs:514-515` has the same defect in milder
form: `-bios default` (OpenSBI) *plus* `-kernel`.

## What in-guest Vulkan would require

Extends, does not duplicate,
`doc/08_tracking/bug/simpleos_vulkan_board_gap_venus_is_qemu_only_2026-08-06.md`
and the G0/G1 plan `doc/04_architecture/os/vulkan/simpleos_vulkan_render_backend_plan.md`.

1. A virtio-gpu PCI/MMIO driver in the guest that negotiates the **venus** capset
   (protocol negotiation `vulkan_compositor_backend.spl` explicitly does not
   implement). Today's `detect_virtio_gpu_device` is a `stat` call — see
   `doc/08_tracking/bug/vulkan_detect_virtio_gpu_device_is_existence_check_not_device_probe_2026-08-07.md`.
2. A venus command-ring encoder in pure Simple (no new `rt_*` in C/Rust per repo
   rule), plus guest-side DMA-BUF/shmem allocation for the ring and for images.
3. Removal of the `UNAVAILABLE()` stubs in `freestanding_optional_backends.c`
   *only after* 1-2 exist; today they are the correct fail-closed behaviour.
4. A board story. venus is QEMU-only on the research host, so a board-runnable
   claim needs a real Adreno/Mali/DRM path — closer to the existing
   `src/os/port/qrb2210_adreno_vulkan_kernel_transport.spl` than to venus.

Until 1-4 land, the honest label for any SimpleOS WM frame is `renderer=cpu`.

## Related fail-open already filed

`doc/08_tracking/bug/engine2d_vulkan_window_8k_gate_is_device_present_proxy_2026-08-31.md`
— `check-engine2d-vulkan-window-8k.shs` passes via `scope=xvfb-device-present-proxy`
with `readback_bytes=0` and captures no pixels. Same failure mode this record exists
to prevent.

## Blocker hit while producing pixel evidence

The x86_64 WM lane (`check-simpleos-x86-64-wm-hello-lifecycle-evidence.shs`) refuses
to run without an **admitted Stage-2 compiler**: `SIMPLE_BIN` defaults to
`build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple` and is
gated by `simpleos_admitted_runtime_verify_auto`
(`scripts/check/lib/simpleos-admitted-runtime.shs`), which requires an
`admission.env` receipt chain plus a live env-ABI probe. A stale deployed
`bin/release/.../simple` fails at exit 11 (`simple-bin-admission-or-env-abi-failed-11`),
and a bare `cargo build --release --bin simple` seed cannot satisfy it either —
it has no receipts. Producing WM pixel evidence in a fresh worktree therefore
requires a full bootstrap first.
