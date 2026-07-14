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

On 2026-07-11 a current-source RV64 kernel passed live HTTP and same-boot DB
CREATE/INSERT/SELECT; see
`doc/09_report/verify_simpleos_filesystem_toolchain_servers.md`. Fresh checkouts
do not retain its ELF, serial log, or DB transcript, so rebuild and rerun without
`--allow-prebuilt-artifact` before making a fresh-current-evidence claim.

With `--with-db`, `scripts/qemu/qemu_rv64_http_test.shs` now sends three real
`POST /db` requests in one guest boot: create `codex`, insert `answer=codex-41`,
then select it. It passes only when all three HTTP responses succeed and the
selected body contains `codex-41`. The retained-evidence checker likewise
requires three `200` responses plus `OK CREATE`, `OK INSERT`, and `codex-41`;
it also rejects negative response lengths. The producer writes the three raw
responses to `db_query.log` beside `SERIAL_LOG`, so a custom
`SERIAL_LOG=/artifacts/serial.log` directly creates the checker layout. Serial
readiness alone cannot pass. This proves networking and state across requests
within one boot only: `SimpleDbService` stores rows in module memory and the
wrapper recreates the attached storage image. Filesystem and reboot persistence
remain unproven.

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

This is an RV64 VirtIO scanout transport probe, not a production WM lifecycle
gate. `display_entry.spl` prints its WM/Engine2D/Web markers unconditionally and
the C runtime paints the five fixed anchors. Preserve the QMP result as
scanout evidence only; production RV64 `SharedWmScene`/Engine2D evidence remains
open under TODO 565 and the dynamic display-owner migration under TODO 567.

## Host-GPU rendering and ProcessingIR

The canonical multi-ISA wrapper is:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test-metrics
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --validate-report build/simpleos_host_gpu_2d/report.env
```

Before building a guest, both the wrapper and `_QemuRunner` require a
candidate pure-Simple compiler to complete
`check test/05_perf/io_parity/startup_simple.spl` successfully within a
10-second deadline. Unix allows a one-second forced-kill grace for a process
that ignores termination; Windows force-kills at its bounded wait deadline. A
timeout, signal, or nonzero exit rejects the candidate even when it passes the
version and native-build argument probes; this prevents stale-ABI artifacts
from reaching the QEMU build path.

It builds `simpleos-host-gpu-x86_64`, `simpleos-host-gpu-aarch64`, and
`simpleos-host-gpu-riscv64` through `_QemuRunner`, starts the strict host
daemon over one bounded ivshmem region per row, and requires the existing
64x48 raw-render, Draw IR, and independent ProcessingIR device-readback probe.
The AArch64 row has a second mandatory phase: after that probe passes, the
wrapper boots `arm64-desktop-engine2d` while retaining the same daemon, shared
memory file, and RSS metrics file. Each QEMU phase is sampled concurrently with
the daemon, and the daemon, QEMU, and combined maxima carry across both boots.
The production phase does not replace or
weaken the 64x48 probe. Its ready generation must continue the probe's final
ProcessingIR generation according to the shared Metal, DirectX, then Vulkan
negotiation order, proving both boots used one daemon session rather than two
independent valid logs.

The second QEMU argument vector must have this exact token shape (with the
row-owned shared-memory path substituted for `<row-shm>`):

```text
-machine virt -cpu cortex-a72 -m 512M
-kernel build/os/simpleos_arm64_desktop_engine2d.elf
-nographic
-device ramfb
-device virtio-net-pci
-object memory-backend-file,id=hostgpu,share=on,mem-path=<row-shm>,size=8M
-device ivshmem-plain,memdev=hostgpu
```

A production pass requires the serial
sequence `[wm-frame] host-gpu-ready` -> `[wm-frame] host-gpu-presented` ->
`[desktop-gui] first-frame-rendered` ->
`[desktop-gui-arm64] desktop-ready`, together with successful RAMFB
configuration. The selected backend must match the host contract; the
presented run must equal the ready generation; the presented generation and
frame must be equal and exactly one newer; its checksum must be positive; and
the two desktop revisions must be equal and positive.

Linux Vulkan rendering and the native CUDA ProcessingIR executor are
implemented with Vulkan ProcessingIR fallback;
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
The additive `arm64-desktop-engine2d` scenario supplies the canonical
RAMFB/`DesktopShell` build target, and the wrapper source now defines the
correlated production-frame gate above. TODO 548 still blocks a fresh build and
execution, so this source-level contract is not a fresh live PASS.
Cached reports are accepted only through `--validate-report`: an overall status
cannot promote the lane unless all nine host/ISA rows are well-formed and a
passing active host carries three existing serial logs with exact correlated
render, Draw IR, and ProcessingIR receipts. A passing active AArch64 row must
also carry its production serial-log and exact production-argv evidence keys;
cached reports created before those keys existed are invalid and cannot be
promoted. Every passing row must also contain
the actual QEMU version, a reversible comma-delimited per-argument hex encoding
of its exact argument vector, positive maximum-observed daemon RSS, QEMU RSS,
and concurrent combined RSS (no smaller than either component), protocol
version, positive operation timings, and matching run/frame identities. The
validator checks the encoded token sequence against the ISA-specific machine,
kernel basename, and exact shared `hostgpu` object/device binding; a syntactic
hex string with the wrong QEMU semantics fails. It also rejects missing,
duplicate, empty, nonpositive, or inconsistent fields. The isolated metrics
self-test exercises malformed values and the two-phase maximum carry without
starting QEMU or a compiler. Fresh live rows are still required before claiming
the latency or 256 MiB combined QEMU-plus-daemon RSS targets. The 64x48 protocol
fixture does not satisfy NFR-001's selected 1280x720 dimensions (TODO 569), and
exact ProcessingIR parity alone does not satisfy NFR-004's 1.5x preference
threshold (TODO 570).

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
