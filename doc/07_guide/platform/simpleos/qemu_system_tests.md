# QEMU System Tests Guide

## Overview

System-level SSpec tests for SimpleOS boot and execution live in `test/03_system/os/qemu/`. Each test boots a real QEMU instance per architecture, executing full end-to-end scenarios. The helper contract is defined in `src/os/qemu_systest_contract.spl`.

## Running System Tests

Export the Simple compiler path, then invoke a specific test:

```bash
export SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed
bin/simple test test/03_system/os/qemu/sys_qemu_riscv64_fs_exec_spec.spl
```

The bootstrap driver is required because system-level tests execute compiled binaries, not interpreter mode.

## Production Desktop DrawIR Path

The x86 desktop source entry creates one persistent `Engine2dWmFrameExecutor` and
passes it to `DesktopShell.render_baremetal_first_frame` and
`DesktopShell.run_baremetal`. Each changed frame is a canonical
`DrawIrComposition`; top-level Simple Web/GUI pixels are request-scoped resolved
IMAGE resources validated by revision, dimensions, exact pixel count, checksum,
and unique URI before presentation. Nested content currently fails closed. The
executor maps the bounded ivshmem BAR into the active VMM and tries the existing
host Draw IR bridge first; only a correlated device receipt followed by checked
MMIO presentation succeeds, and every other case falls through to local
Engine2D. The current 3840x2160 frame exceeds the 8 MiB wire, so TODO 552 keeps
that default entry honestly local without downscale or crop.
This source path is not compile-verified while TODO 548 blocks the pure-Simple
checker; no QEMU receipt is claimed by this section.

## Direct Boot Fallback

While P1 system-test automation is open, use direct `qemu-system-*` commands for manual verification. This is the known-good riscv64 boot command:

```bash
qemu-system-riscv64 \
  -machine virt \
  -m 512M \
  -nographic \
  -bios default \
  -global virtio-mmio.force-legacy=false \
  -drive file=build/os/fat32-riscv64.img,if=none,id=rvdisk,format=raw \
  -device virtio-blk-device,drive=rvdisk \
  -kernel build/os/simpleos_riscv64_smf_fs.elf
```

## Pass Markers

Serial output must contain ALL of these to qualify as a pass:
- `SIMPLEOS_RISCV_SMF_FS_PASS`
- `TEST PASSED`
- `ELF_LOAD_OK`
- `SMF_CLI_LAUNCH_OK`

**Fail-closed rule:** Serial output containing either of these is NEVER a pass, even if other markers are present:
- `[launcher] fallback=resident-manifest`
- `[desktop-e2e] resident-fallback:active`

See `src/os/fs_exec_fallback_contract.spl` for the full fallback contract.

## Telnet-over-Serial Observation

A system test can observe the guest console over a telnet socket instead of
reading the serial file directly, exercising the same path a real board would
use. `scripts/qemu/check_simpleos_riscv_telnet_serial.shs` boots SimpleOS RV64
on `qemu-system-riscv64 -machine virt` (OpenSBI) with `-serial file:$rx`, then
the telnet-over-serial bridge (`std.nogc_sync_mut.io.telnet_serial_bridge`)
relays `$rx` to a TCP telnet port where a telnet client waits for a real kernel
marker (`SimpleOS RV64`). The QEMU `-serial file:` output *is* the bridge's
read path — no glue needed. This is the emulation counterpart of the physical
KV260 path in `doc/07_guide/hardware/fpga/kv260_rv64gc_fpga_boot.md` (Section 8);
point `QEMU_RX`/`SERIAL_PORT` at a real tty to validate silicon with the same
harness.

## x86 SSH Host Forwarding

The live x86 SSH smoke maps the host TCP endpoint to the guest-facing QEMU
forwarded port. OpenSSH connections that reach the guest as destination port
`2222` are accepted by the kernel's SSH listener on port `22`; the accepted
socket then keeps the real packet destination port so replies match the
host-forwarded flow.

Keep this contract covered by
`test/01_unit/os/x86_ssh_boot_tcp_contract_spec.spl` when editing the x86
baremetal TCP listener path. The live SSH gate is
`test/03_system/os/ssh_live_login_in_qemu_spec.spl`; a TCP accept or banner
exchange pass is not a full SSH pass unless the later KEX/auth/session checks
also complete.

## Known Blockers

The `/bin/simple os` subcommands (e.g., `bin/simple os test`) are currently broken per `doc/08_tracking/bug/interp_simpleos_lane_contract_crash_2026-06-13.md`. System tests therefore boot `qemu-system-*` directly rather than through the compiler tool.

## Alpine-Class Hardening Specs (RED until build target exists)

Three new specs in `test/03_system/os/qemu/os/harden/` exercise the SimpleOS x86_64 hardening
probe. All classify MISSING-MEDIA (RED) until `build/os/simpleos_x86_64_harden_probe.elf` and
`build/os/fat32-x86_64-harden.img` are produced by the harden probe build target
(see `doc/08_tracking/bug/simpleos_harden_probe_build_target_2026-06-28.md`).

| Spec | AC | Markers |
|------|----|---------|
| `os/harden/cap_exec_gate_spec.spl` | AC-1 | `[exec] capability gate: ENFORCED`, `[exec] uncapable exec REJECTED` |
| `os/harden/hardened_malloc_spec.spl` | AC-2 | `[hmalloc] guard-page trap OK`, `[hmalloc] double-free TRAPPED` |
| `os/harden/pie_ssp_relro_preset_spec.spl` | AC-8/9/10 | `[hardening] PIE=1`, `[hardening] RELRO=1 BIND_NOW=1`, `[hardening] NX=1 SMEP=1 SMAP=1`, `[hardening] STACK_CANARY=1` |

Each spec follows the standard fail-closed contract: a media-check `it` (expects `rt_file_exists`
true for kernel + image) followed by a boot `it` (calls `run_qemu_systest`, expects `== SYSTEST_PASS`).
Missing media returns `missing-media:<path>` — never `skip()`.

## Storage Policy

FAT32 images (~4 MB each) and kernel ELFs are kept for reproducibility and regression testing. QMP logs and .ppm screendumps are stale debris.

Run the audit script to see per-category disk usage:

```bash
scripts/check/qemu-storage-audit.shs        # Dry run
scripts/check/qemu-storage-audit.shs --clean # Delete QMP logs and .ppm >7 days old
```

Serial logs and test output remain in `build/os/systest/` for diagnosis.

## RV64 HTTP/Display Probe Diagnostics

`scripts/qemu/qemu_rv64_http_test.shs` accepts env overrides for short,
bounded diagnostics:

```bash
BOOT_TIMEOUT=3 SERIAL_TAIL_LINES=20 \
  sh scripts/qemu/qemu_rv64_http_test.shs --expect-http-only --with-display --with-storage --with-db
```

On failure the wrapper prints only the serial tail. This keeps repeated RV64
banner loops from flooding the calling session.

As of 2026-07-11 the retained HTTP transcript is historical only. A fresh
`bin/simple os build --arch=riscv64` fails because the deployed compiler is the
Rust seed without LLVM, and `build/os/simpleos_riscv64.elf` is absent. Do not use
`--allow-prebuilt-artifact` for a current-source claim.

With `--with-db`, `scripts/qemu/qemu_rv64_http_test.shs` now sends three real
`POST /db` requests in one guest boot: create `codex`, insert `answer=codex-41`,
then select it. It passes only when all three HTTP responses succeed and the
selected body contains `codex-41`. The retained-evidence checker likewise
requires three `200` responses plus `OK CREATE`, `OK INSERT`, and `codex-41`;
it also rejects negative response lengths. The producer writes the three raw
responses to `db_query.log` beside `SERIAL_LOG`, so a custom
`SERIAL_LOG=/artifacts/serial.log` directly creates the checker layout. Serial
readiness alone cannot pass. A current-source QEMU run is still blocked until
the RV64 ELF can be rebuilt by the self-hosted compiler.

Without `--allow-prebuilt-artifact`, the wrapper also requires a build stamp
newer than the ELF and rejects `simple_bin` provenance naming `compiler_rust`
or `simple_seed`. Seed-built and stale-stamp kernels remain diagnostic only.

When `nm` is available, the wrapper also fail-fast checks the RV64 ELF before
launch. If `_start` aliases `rt_riscv_uart_put`, the artifact is the known
native entry-closure symbol-mismatch build and QEMU evidence is not useful until
the RV64 native-build source-worker path is fixed.

## RV64 SMF GUI Serial vs Framebuffer Evidence

The current-source RV64 SMF filesystem smoke is:

```bash
bin/simple os build --arch=riscv64
timeout 20s qemu-system-riscv64 -machine virt -cpu rv64 -m 256M \
  -nographic -bios default -no-reboot \
  -kernel build/os/simpleos_riscv64_smf_fs.elf
```

A pass prints `SMF_WM_GUI_LAUNCH_OK`,
`NATIVE_GUI_PROCESS_RENDER_OK`, `SIMPLEOS_RISCV_SMF_FS_PASS`, and
`TEST PASSED`, and QEMU exits with status `0`. The host configuration matrix
reports this as `simpleos_host_configuration_qemu_riscv64_smf_gui_serial_status=pass`.

This is not RV64 live WM framebuffer evidence. The framebuffer gate remains
open until an RV64 display-entry ELF stays alive long enough for QMP or an
equivalent capture to prove nonblank WM pixels.

The display-capable full boot lane is exposed as:

```bash
bin/simple os build --scenario=riscv64-smoke
```

That scenario routes to `src/os/kernel/arch/riscv64/boot.spl` and
`build/os/simpleos_riscv64.elf`, the lane that calls
`riscv_noalloc_services_init(true)` and can reach the RV64 virtio-gpu display
service. Current evidence: the route is valid, but the full native-build still
exceeds a 240s bounded build probe before producing the ELF.

For a smaller framebuffer bring-up target, use:

```bash
bin/simple os build --scenario=riscv64-display-smoke
RV64_DISPLAY_SMOKE_BUILD=0 scripts/check/check-rv64-display-smoke-qmp-evidence.shs
```

This routes to `examples/09_embedded/simple_os/arch/riscv64/display_entry.spl`
and `build/os/simpleos_riscv64_display_smoke.elf`. The entry calls only the
RV64 display runtime (`rt_display_init`, `rt_display_flush_wm_anchor_test`) and then idles
for QMP capture. Current evidence: `bin/simple os build
--scenario=riscv64-display-smoke` emits the ELF, direct QEMU serial reaches
`SIMPLEOS_RISCV_DISPLAY_SMOKE_READY`, and QMP `screendump` captured a nonblack
320x240 PPM at
`build/os/rv64_display_smoke_evidence-current/screendump.ppm`. Current report:
`doc/09_report/rv64_display_smoke_qmp_evidence_current_2026-07-02.md`.

This is the RV64 freestanding WM lifecycle gate used by the host configuration
matrix. The host configuration and hardening matrices report
`simpleos_hardening_rv64_display_smoke_qmp_status=pass` when the wrapper sees
the WM lifecycle serial markers, a nonblack QMP PPM, and all five WM anchor
sample pixels.

## Host-GPU rendering and ProcessingIR

The canonical multi-ISA wrapper is:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --validate-report build/simpleos_host_gpu_2d/report.env
```

It builds `simpleos-host-gpu-x86_64`, `simpleos-host-gpu-aarch64`, and
`simpleos-host-gpu-riscv64` through `_QemuRunner`, starts the strict host
daemon over one bounded ivshmem region per row, and requires exact Vulkan
render plus ProcessingIR device readback. Linux Vulkan rendering and the native
CUDA ProcessingIR executor are implemented with Vulkan ProcessingIR fallback;
refreshed cross-ISA CUDA receipts
are still required. macOS Metal Draw IR execution is implemented but remains
`unsupported` evidence until a prepared native host produces a fresh receipt.
Metal ProcessingIR FillU32 is implemented through a dedicated checked MSL
kernel and device readback, but likewise needs a prepared-host receipt. Windows
DirectX/CUDA rows remain `unsupported` evidence until a prepared host produces
fresh receipts; a bounded native D3D11 owner is implemented, but its API name
alone is not proof. The host Draw IR executor retains the parent Vulkan or Metal
session for bounded smaller WM surfaces, requires child device readback, and
applies canonical embedding opacity through checked native parent src-over.
The current wrapper fixture remains
full-frame, so fresh production-WM QEMU evidence is still required even though
the production selection seam is wired.
Cached reports are accepted only through `--validate-report`: an overall status
cannot promote the lane unless all nine host/ISA rows are well-formed and a
passing active host carries three existing serial logs with exact correlated
render, Draw IR, and ProcessingIR receipts. Every passing row must also contain
the actual QEMU version, a reversible comma-delimited per-argument hex encoding
of its exact argument vector, positive maximum-observed daemon RSS, protocol
version, positive operation timings, and matching run/frame identities. The
validator checks the encoded token sequence against the ISA-specific machine,
kernel basename, and exact shared `hostgpu` object/device binding; a syntactic
hex string with the wrong QEMU semantics fails. It also rejects missing,
duplicate, empty, or nonpositive fields; fresh live
rows are still required before claiming the latency or combined QEMU-plus-daemon
RSS targets.

Processing receipts distinguish the transient backend resource handle from the
stable device identity. Vulkan hashes the runtime-selected driver identity,
which includes the device name and driver metadata, and negotiation fails
closed when it is missing. CUDA prefers the MIG-aware v2 UUID API with legacy
fallback, rejects the all-zero sentinel, and the native gate requires repeated
reads to agree (and multiple devices to remain distinct);
an ordinal, compute capability, or buffer handle alone is not device provenance.
Metal hashes validated default-device metadata and is advertised only after a
real nonzero FillU32 probe returns exact device bytes, a positive handle, and
identity.
The guest bridge captures the completion once and validates its typed receipt,
including the device readback source and run/frame/backend correlation. Host
and guest checksum loops share the same masked modular checksum primitives.
