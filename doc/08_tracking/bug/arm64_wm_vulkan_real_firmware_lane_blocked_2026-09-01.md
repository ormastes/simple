# arm64 WM+Vulkan real-firmware smoke lane is blocked: `arm64-desktop-engine2d` scenario is unregistered (2026-09-01)

Status: **OPEN** (Blocker 1 FIXED 2026-09-01, gate still ERROR).
Gate landed **ADVISORY** (honestly RED).

**Update 2026-09-01:** Blocker 1 is fixed — `arm64-desktop-engine2d` is now
registered and `os build --scenario=arm64-desktop-engine2d` dispatches instead
of saying `unknown scenario`. Three further pre-existing blockers were found
behind it and the kernel is still unproducible; Blocker 2 (real-firmware
`protocol: linux` handover) remains UNPROVEN because no boot was reached. See
`arm64_desktop_engine2d_media_chain_blockers_2026-09-01.md`.
Gate: `scripts/check/check-simpleos-arm64-wm-vulkan-pixel-evidence.shs`
Arch scope: aarch64/arm64 only. x86_64 and riscv64 are other lanes.

## Summary

Goal item 2 asks for an "x86, arm, riscv simple os wm with vulkan backed smoke
test". The aarch64 gate is written and its `--selftest` is green (25 fixtures,
including a banner-only must-FAIL), but it **cannot reach a boot** because the
arm64 desktop/WM kernel **cannot be built at all**.

Real run, this worktree, 2026-09-01:

```
[arm64-wm-vulkan] selftest OK (25 fixtures)
ERROR — nothing was checked: arm64 desktop/WM kernel missing:
  build/os/simpleos_arm64_desktop_engine2d.elf — build it first with
  scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs
```

## Blocker 1 (primary, hard) — the scenario is defined nowhere it can be dispatched

`scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs:399` runs

```
"$COMPILER" os build --scenario=arm64-desktop-engine2d
```

Measured result:

```
Error: unknown scenario 'arm64-desktop-engine2d'
```

Root cause, from source (not inference):

- `src/os/_QemuRunner/runner_targets.spl:558` defines
  `get_arm64_desktop_engine2d_target()` — entry
  `examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl`, output
  `build/os/simpleos_arm64_desktop_engine2d.elf`.
- `/usr/bin/grep -rn get_arm64_desktop_engine2d_target src/` returns **exactly
  one line — its own definition. Zero callers.**
- `src/os/_QemuRunner/scenario_catalog.spl` registers `arm64-wm-ramfb`
  (`:520`, `:843`, `:908`) but has **no `arm64-desktop-engine2d` entry at all**.
  `scenario_exec.spl:784` branches on the name, so downstream code was written
  expecting a registration that was never made.
- `test/01_unit/os/gui_entry_desktop_production_render_contract_spec.spl:142`
  asserts the catalog contains
  `_scenario_from_target("arm64-desktop-engine2d", get_arm64_desktop_engine2d_target()`
  — i.e. the spec already encodes the missing registration.

So the entire arm64 desktop/Engine2D lane — the attested builder, and every
gate downstream of it — is **dead on arrival**, not merely unbuilt. No stale
binary or environment gap is involved; a fresh `origin/main` worktree cannot
produce this kernel.

**Fix:** register the scenario in `scenario_catalog.spl` alongside
`arm64-wm-ramfb`, wiring `get_arm64_desktop_engine2d_target()`. Deliberately
not done in this change: it is a product-code edit to a shared runner touched
by other lanes, and it needs its own reproduce spec plus the neighbours in
`gui_entry_desktop_production_render_contract_spec.spl` re-run.

## Blocker 2 (secondary, not yet reached) — real-firmware handover unproven for this kernel

`.claude/rules/board-runnable.md` requires EDK2/AAVMF pflash ->
`vendor/limine/BOOTAA64.EFI` -> `kernel.elf`; never QEMU `-kernel`.

- The building blocks exist and the gate uses them:
  `scripts/os/build-simpleos-aarch64-efi-esp.shs` already supports
  `BOOT_PROTOCOL=linux` + `KERNEL_ELF=` for exactly this kernel, and
  `scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs` proves the
  chain with the marker kernel.
- But the *only* aarch64 kernel ever booted through that chain is the Limine
  milestone/marker kernel. The desktop target
  (`runner_targets.spl:558`) links with
  `examples/09_embedded/simple_os/arch/arm64/linker.ld`, the `-kernel` script.
  Per CLAUDE.md the arm64 `crt0.S` Linux `Image` header + self-relocation stub
  should make `protocol: linux` handover work with that same script, but this
  has **never been executed with the desktop kernel** — it could not be,
  because of Blocker 1. Do not record it as proven.

## Vulkan reality (honest statement — no stub is being called Vulkan)

- **Host:** real. `vulkaninfo --summary` on this host reports
  `NVIDIA TITAN RTX`, `apiVersion = 1.4.312`, `driverName = NVIDIA`. Not
  lavapipe, not a stub. "No GPU on this host" would be false.
- **Guest:** there is **no in-guest Vulkan on aarch64, and never was.**
  `src/os/compositor/vulkan_compositor_backend.spl` rejects every draw by its
  own contract, and `rt_vulkan_*` is compiled out in the freestanding guest
  (see `simpleos_in_guest_vulkan_absent_wm_smoke_is_cpu_2026-08-31.md`).
- **What "Vulkan-backed" therefore means on aarch64:** a guest -> host
  **offload**. `arch/arm64/gui_entry_desktop.spl:208` wires
  `Engine2dWmFrameExecutor.create_host_gpu(..., SIMPLEOS_HOST_GPU_ISA_AARCH64, ...)`
  over an ivshmem BAR, and `arch/arm64/gui_entry_desktop_linux_qemu.spl`
  requests `SIMPLEOS_HOST_GPU_BACKEND_VULKAN` with `backend_required: true`.
  The host daemon `src/app/simpleos_gpu_host/` executes the draw IR on the real
  host GPU.
- The gate prints `..._renderer=host-vulkan|cpu` and
  `..._host_vulkan_driver=hardware:<name>|software:<name>` on their own lines
  and inside the verdict, so a software ICD can never be quoted as a hardware
  GPU, and a CPU-drawn frame can never be quoted as Vulkan.

## How the gate refuses to fake a pass

- Verdict is the last stdout line: `PASS — <n> item(s) checked ... renderer=…`
  (0) / `FAIL — …` (1) / `ERROR — nothing was checked: …` (2). Zero captured
  frames, missing firmware, a failed build, or an empty serial log is ERROR.
- `--selftest` is fatal and runs before every scan (25 fixtures), including the
  **banner-only must-FAIL**: both logs carry well-formed Vulkan banners with no
  anchored per-boot `frame`/`submit_id`/`fence_id` triple, and must classify as
  `cpu`.
- Per-run nonce + fresh-volume anchoring, checked on raw BYTES host-side: the
  freshly built `esp.img` and the freshly zeroed ivshmem backing file are
  grepped pre-boot for the run nonce and for the evidence target path. Any hit
  is ERROR.

  Receipt BANNERS are deliberately **not** part of that volume check. They are
  format literals in the WM kernel's rodata and the ESP carries `kernel.elf`;
  measured on the x86 sibling's real desktop kernel,
  `grep -ac 'desktop-ready'` and `grep -ac 'host-gpu-presented'` both return 1.
  Banning them on the volume would have made this gate permanently un-passable
  on any legitimately built image. Their staleness is instead fenced by the
  per-boot frame/submit/fence triple, which a rodata string cannot satisfy —
  and a selftest fixture pins exactly this: a volume carrying only the
  compiled-in banners must read as CLEAN, while the banner-only *log* fixture
  must classify as `cpu`.
- `renderer=host-vulkan` needs the guest serial receipt and the host daemon
  receipt to name the **same per-boot triple**; a stale daemon log, a different
  frame, a different submission, a `backend=cpu` receipt, a guest-emitted
  `HOST_GPU_PROCESS_OK`, or a compute-path `HOST_GPU_PROCESS_PERF` all
  classify as `cpu`. Each is a selftest fixture.
- The QEMU argv is self-scanned for `-kernel` and `isa-debug-exit` immediately
  before execution; both are also must-FAIL selftest fixtures.
- `SIMPLE_ALLOW_STUB_FALLBACK` / `SIMPLE_ALLOW_UNRESOLVED_RUNTIME` are never
  set; the daemon `native-build` runs with `--timeout 1200` and
  `SIMPLE_NO_STUB_FALLBACK=1`, and its exit code is captured directly into a
  variable, never through a pipe.

## Promotion criteria

Promote from ADVISORY to MANDATORY when, in one run on a clean `origin/main`
worktree, the gate prints `PASS — <n> item(s) checked ... renderer=host-vulkan`
with `host_vulkan_driver=hardware:<name>`. That requires, in order:

1. Register `arm64-desktop-engine2d` in `scenario_catalog.spl` (Blocker 1).
2. Build the kernel via the attested builder.
3. Confirm `protocol: linux` handover of that kernel from `BOOTAA64.EFI`
   (Blocker 2), and that it reaches `[desktop-gui-arm64] desktop-ready`.
4. Confirm the ivshmem offload negotiates so the dual receipt anchors.

## What IS already proven by this change

Running the gate with a deliberately junk kernel exercises the real ESP path
end to end and it works: real `/usr/share/AAVMF/AAVMF_CODE.fd` +
`AAVMF_VARS.fd` are found and staged, `vendor/limine/BOOTAA64.EFI` is present,
`mkfs.vfat` builds the FAT image, and the builder only fails when asked to
stage the junk payload —

```
ERROR — nothing was checked: ESP build failed (rc=1, ...):
  build-aarch64-efi-esp: ERROR — populating the FAT image failed
```

i.e. the failure is correctly reported as ERROR (exit 2) with a verdict line,
not as a bare non-zero exit. The only missing input to a real boot is the
kernel, which is Blocker 1.
