# QEMU System Tests Guide

## Overview

System-level SSpec tests for SimpleOS boot and execution live in `test/03_system/os/qemu/`. Each test boots a real QEMU instance per architecture, executing full end-to-end scenarios. The helper contract is defined in `src/os/qemu_systest_contract.spl`.

## Running System Tests

Use a current pure-Simple self-hosted compiler, then invoke a specific test:

```bash
bin/simple test test/03_system/os/qemu/sys_qemu_riscv64_fs_exec_spec.spl
```

The Rust seed is bootstrap-only and is not a test fallback. If `bin/simple`
cannot resolve a valid current self-hosted compiler, record the compiler blocker
and stop; do not point `SIMPLE_BOOTSTRAP_DRIVER` at `simple_seed` to turn a
blocked system-test row into apparent evidence.

## RV64 Ordered Boot-Gate Lane

The canonical completion contract for Sv39, PID1, network, production SSH, and
process-owned WM is
`doc/03_plan/sys_test/rv64_ssh_live_login_in_qemu.md`. It supersedes any claim
based only on the older banner/probe/rectangle desktop-service fixture.

The admitted serial order is Sv39 readback, live PID 1, VirtIO TX, VirtIO RX,
network service, production SSH bind/listen, correlated session completion and
accept recovery, then a PID-correlated WM presented frame. The shared pure
checker (`Rv64BootGateState`, `rv64_boot_gate_advance`, and
`rv64_boot_gate_verdict`) must reject missing, duplicate, or reordered
observations. The host evidence owner emits the sole terminal `TEST PASSED`.

OpenSSH evidence uses separate real sessions for `true`, `simple --version`,
and `simple.smf --version`, followed by bad-password rejection and a later
successful connection. Every completed or rejected session must have its own
accept-resumed correlation receipt. A fixed combined command, canned stdout, banner-only socket,
marker-only PID1, or fixed rectangle/string WM fixture is not production boot
evidence.

As of 2026-08-14 this lane has no provenance-admitted Stage 4 full CLI.
Historical cycle 3 published Stage 2 (binary SHA-256
`e383d2c6ea86e63ba6805cf3478f723cecd673c2e141be86b3cf1150d14e9378`,
log SHA-256
`db7907064858b472ffadf3cc9527f73acfaf4e80a5f3156d203ba84b924fb167`).
Host `earlyoom` then sent Stage 3 SIGTERM at 41,394 MiB RSS on a no-swap host
with less than 10% free memory; exit 143 followed 5.4 seconds later. No Stage
3/4, deployment, rollback, or essential smoke occurred. That Stage 2 predates
the complete `d99deb3` snapshot runtime provider. TODO666 is open/actionable:
the incompatible M0 draft was reverted, while resume-only durable sinks remain.
Safe phase publication, full-bootstrap wiring, supervisor/provenance migration,
a fresh current-HEAD Stage 2, and one
instrumented Stage 3 in a fresh session; the 41,394 MiB value is an interrupted
high-water mark, not a proved RAM requirement. TODO667/A2 remains gated.
The current source lanes B-F are integrated; this statement blocks executable
evidence only, not additional speculative source rewrites. In particular, the
IPC/VFS wave has syscall-18 owner-only destruction, named-service discovery,
anonymous reply ports, bounded copied frames, public FS binary decoding,
manager-owned mutations, POSIX access-mode flags and FD READ/WRITE/SEEK/close; WM/Window send item-zero
bytes and SSH filesystem-exec lifecycle are integrated too. TODO808 retains
the bounded stdout/status cases, TODO809 retains PID/frame evidence, TODO806
owns the combined live row, and TODO807 owns maintain/docgen/manual review.

P1c fixes the service boundary without creating a second wire protocol:
`IPC_COPIED_SERVICE_TAG` is the sole copied-message discriminator and all
other values retain the legacy send ABI; `IpcDestroyPort` permits only the
recorded owner to revoke a live port. VFS close remembers terminal handles by
a monotonic issue watermark, so repeated confirmed closes are idempotent
without an unbounded tombstone list; a lost close reply preserves the final
local FD for retry. SOSIX `io.spl` and `io_rw.spl` converge on the shared named
VFS owner and the current READ/WRITE/SEEK frames. After TODO667, execute once
the canonical IPC-handoff, destroy-port, VFS-wire, `fd_io_route`, and
`sosix/io` rows from the plan, retain their output and Stage 4 provenance, and
hand them to the primary RV64 merge owner and normal/highest-capability Codex
reviewer. They are focused source-contract evidence only; TODO806 is still the
remaining combined QEMU runtime blocker.

The boot owner also validates SATP mode and root PPN against the activated
Sv39 root, keeps the daemon accepting after the first WM frame, and validates
terminal handling plus accept recovery for every later accepted session. These
strengthen AC-3/AC-4/AC-6 source status but remain unexecuted obligations.

Terra's 2026-08-14 terminal-only diagnostics do not relax this rule. The
release binary checked `ssh_live_entry.spl` and the WM-resource spec with exit
0, and the WM-resource interpreter spec exited 0 with empty output; the IPC
handoff focused run was reported PASS. Those outputs were not retained under
the canonical artifact root, so they are not Stage 4, system, or QEMU receipts.
The release binary then printed `Checking...` and segfaulted while loading
`rv64_ssh_live_login_in_qemu_spec.spl`; no core/log was retained. Preserve the
next attempt's terminal output and provenance, run it only after TODO667, and
never represent either the narrow PASS diagnostics or the checker crash as a
live lifecycle verdict.

The successful cycle-3 transaction runs the canonical essential-tools smoke
internally exactly once and retains `stage4-essential-tools-smoke.log`; do not
repeat it as a standalone smoke. Keep that deployment active through the
source-matched focused/live rows; only afterward use the existing
`sh scripts/bootstrap/rollback-bootstrap-deploy.shs x86_64-unknown-linux-gnu`
and retain its rollback receipt. Earlier rollback requires TODO667's isolated
immutable bundle and all downstream rows must execute from that bundle.

The remaining execution wave is deliberately parallel after Stage 4
admission: IPC/VFS/SOSIX, boot-owner, SSH, WM, and SSpec/manual owners write
disjoint focused logs. The combined QEMU/OpenSSH/QMP run is then serial because
it owns fixed port 2222 and the canonical live artifact paths. AC-8/AC-9
documentation is accepted by the H0/root static review and has no runtime
dependency. The earlier reachable `WARN` receipt proves
only the source handoff; final AC-10 still requires a post-acceptance `PASS`
receipt.

## Engine2D Exact-Oracle Gate

TODO529 is governed by
`doc/03_plan/sys_test/engine2d_qemu_exact_oracle.md`. The executable spec must
use the pure-Simple QMP capture and exact comparison owners, reject a missing
independently reviewed oracle, and fail rather than skip when a required QEMU
target is unavailable. x86_64, AArch64, and RV64 require separate guest-native
entries and retained serial/capture evidence; an x86-only pass cannot close the
TODO.

Do not add Python capture, `rt_process_run*`, direct `rt_env_get`, tolerance,
automatic baseline creation, or `UPDATE_BASELINE` behavior to this gate. While
the current pure-Simple compiler is unavailable, the live rows remain blocked;
source inspection or a cached PPM is not a QEMU PASS.

## QEMU SIMD Object Gate — Static Prerequisite Tier

`scripts/check/check-simpleos-qemu-engine2d-simd-kernels.shs` is the static
prerequisite for every SimpleOS SIMD backend claim: it compiles the arm64 and
x86_64 baremetal stubs and asserts the emitted `rt_gui_fill4` actually contains
NEON (`dup`, `st1`) and SSE2 (`pshufd`, `movdqu`) instructions plus the
`rt_gui_simd_fill_*` receipt symbols. Passing it does **not** mark a backend
verified — guest hit/chunk receipts and QMP captures remain mandatory.

**Read the gate's own exit status, never a pipeline's.** On 2026-08-16 this
gate was found exiting 1 with **zero lines of output**: its `st1` assertion
used a doubled-backslash ERE, which matches a literal backslash, while
llvm-objdump emits `st1` + tab + `{ v0.4s }, [x0]`. Under `set -eu` the
unmatched `grep -Eq` aborted the script before its three remaining assertions
ran, so the gate had never passed. `sh gate.shs | tail` reports `tail`'s 0 and
hides this completely. Assign the status on the line after the invocation:

```sh
sh scripts/check/check-simpleos-qemu-engine2d-simd-kernels.shs > gate.log 2>&1
rc=$?
```

Repaired at `25dc443e44a`. The regression is now pinned by the step-based
system spec `test/03_system/check/qemu_simd_coverage_gate_lane_spec.spl`
(mirror: `doc/06_spec/03_system/check/qemu_simd_coverage_gate_lane_spec.md`,
plan: `doc/03_plan/sys_test/qemu_simd_coverage_gate_lane.md`), which asserts
the gate's exit status, its non-empty verdict text, the spelling of every
instruction assertion, and — as a negative control — that the historical
over-escaped pattern still matches nothing in real disassembly.

That spec is fail-closed: a host without `clang` or `llvm-objdump` FAILS it.
Do not add a skip path, tolerance, or automatic baseline. Its scenarios have
not yet been executed by a pure-Simple runner; see the TEST_BLOCKED section of
its plan before citing it as a passing result.

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
Exact-size opaque IMAGE work may cross a bounded named child edge: the existing
Vulkan COPY shader clips it to that child without changing DrawIR semantics.
Opaque scaled IMAGE work uses the same checked Vulkan shader with CPU-matching
nearest-neighbor sampling. After opaque initialization, transparent scaled work
uses that shader's checked src-over mode. Fresh compiler/QEMU proof remains TODO 549.
Titled-window DrawIR surfaces include only the positive shadow offsets that fit
inside the scene; body, content, hit, and layout bounds retain window geometry.
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

## Visible-display UEFI boot ladder

`scripts/check/check-simpleos-wm-visible-display-evidence.shs` keeps QEMU alive
from launch through renderer-marker readiness and QMP screendump. It must not
evaluate GRUB or `_start` rungs merely because the QMP socket exists. The normal
observation point is after the shared-renderer serial markers establish that
the serial log exists and is current. Failure paths first quiesce QEMU through
the wrapper’s cleanup owner, then inspect the stable log.

Read the exported ladder fields together:

- `simpleos_wm_visible_display_boot_ladder_status`
- `simpleos_wm_visible_display_boot_ladder_reason`
- `simpleos_wm_visible_display_boot_ladder_observation`
- `simpleos_wm_visible_display_boot_ladder_grub`
- `simpleos_wm_visible_display_boot_ladder_kernel`

`serial-log-not-created-at-check-time` means no file existed at the stable
observation point. `marker-absent-in-existing-serial-log` means a regular log
existed but lacked a rung. Do not report the first state as a marker miss.

Run the no-QEMU contract before a live capture:

```sh
sh scripts/check/check-simpleos-wm-visible-display-evidence.shs --self-test
```

## RV64 Desktop Service/GPU Profile

The multi-config Vulkan/WM lane owns the pure QEMU RV64 desktop descriptor in
`src/os/simpleos_config_matrix.spl`. Use `qemu_riscv64_desktop_qemu_args()` as
the canonical non-hardware contract before wiring live wrappers. The existing
system-test contract exposes the same descriptor through
`src/os/qemu_systest_contract.spl` as `riscv64_desktop_qemu_args()` and
`riscv64_desktop_qemu_args_status()`. It requires:

- host forwarding `tcp::2222-:22` for SSH;
- host forwarding `tcp::8080-:8080` for the SimpleOS webserver;
- `virtio-net-pci,netdev=rvnet`;
- `virtio-gpu-pci,disable-modern=on,disable-legacy=off`;
- headless display with QMP screendump on `127.0.0.1:4444`;
- serial log `build/os/systest/qemu-riscv64-desktop/serial.log`;
- artifact root `build/os/systest/qemu-riscv64-desktop`.

Live wrappers for this profile must emit the rows named by
`simpleos_qemu_service_required_evidence_keys()`:

- `simpleos_qemu_serial_console_status`;
- `simpleos_qemu_rv64_ssh_banner`;
- `simpleos_qemu_rv64_ssh_probe_status`;
- `simpleos_qemu_rv64_http_status_code`;
- `simpleos_qemu_rv64_http_probe_status`;
- `simpleos_qemu_gpu_readback_status`;
- `simpleos_qemu_wm_marker_status`.

`SimpleOsQemuServiceEvidence.status()` is fail-closed: missing serial console,
missing SSH banner/probe, non-200 HTTP, missing HTTP probe, missing GPU
readback, or missing WM marker is a blocked result, not a desktop pass.

On Windows, the focused QEMU RV64 evidence wrapper is:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1
```

It writes raw QEMU service rows to
`build/simpleos_multiconfig_live_evidence/qemu-rv64-desktop.env`. Feed that file
to the aggregate checker:

```powershell
$env:SIMPLE_LIB='src'
src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence build/simpleos_multiconfig_live_evidence/qemu-rv64-desktop.env --mode=interpreter
```

The wrapper is a fail-closed preflight unless a later live boot/probe mode
proves serial console, SSH, HTTP, GPU readback, and WM marker evidence. On the
current Windows host it detects `qemu-system-riscv64.exe` but blocks because
`build/os/simpleos_riscv64_smf_fs.elf` and `build/os/fat32-riscv64.img` are
missing.

Current desktop-service proof on Windows:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1 -BuildDesktopServiceKernel -BuildBackend cranelift -BuildCc C:\dev\install\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin\clang.exe -RunLiveBoot -BootTimeoutSeconds 45
```

This rebuilds `build/os/simpleos_riscv64_desktop_service.elf` and passes the
QEMU service gate with SSH banner, HTTP `200`, QMP screendump/nonblank GPU
readback, and WM marker rows.

To attempt a live QEMU boot after the canonical artifacts exist, run:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1 -RunLiveBoot
```

Live mode writes the same raw service rows plus:

- `simpleos_qemu_rv64_live_boot_requested`;
- `simpleos_qemu_rv64_live_boot_status`;
- `simpleos_qemu_rv64_qemu_exit_status`;
- `simpleos_qemu_rv64_artifact_dir`;
- `simpleos_qemu_rv64_serial_log_path`;
- `simpleos_qemu_rv64_qmp_port`;
- `simpleos_qemu_rv64_qmp_status`;
- `simpleos_qemu_rv64_screendump_path`;
- `simpleos_qemu_rv64_screendump_status`;
- `simpleos_qemu_rv64_screendump_nonblank_status`.

It launches QEMU only after `qemu-system-riscv64`, the canonical SMF-FS kernel,
and the canonical FAT32 image are present. It captures serial output under
`build/os/systest/qemu-riscv64-desktop/serial.log`, waits for RV64 FS-exec or
network/http serial markers, exposes QMP on `127.0.0.1:4444`, and probes SSH
`2222` plus HTTP `8080`. When the serial log reports `Display service ready`,
the wrapper asks QMP for a `screendump` PPM and requires a nonblank P6 image
before setting `simpleos_qemu_gpu_readback_status=pass`. WM serial markers are
diagnostic until paired with that nonblank QMP readback; structured WM compare
and RenderDoc evidence remain separate aggregate gates.

The Engine2D/RenderDoc normalizer also parses that QEMU screendump header when
available and emits `simpleos_qemu_gpu_readback_width`,
`simpleos_qemu_gpu_readback_height`, and
`simpleos_qemu_gpu_readback_dimensions_status`. Those rows are viewport
diagnostics for the QEMU framebuffer; they do not replace
`simpleos_engine2d_runtime_backend=vulkan`.

To collect fresh QEMU RV64 build blocker evidence before live boot, run:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1 -AttemptBuild
```

The build preflight writes
`build/os/systest/qemu-riscv64-desktop/rv64-build.log` and emits:

- `simpleos_qemu_rv64_build_attempted`;
- `simpleos_qemu_rv64_build_status`;
- `simpleos_qemu_rv64_build_exit_code`;
- `simpleos_qemu_rv64_native_build_exit_code`;
- `simpleos_qemu_rv64_build_log_path`;
- `simpleos_qemu_rv64_build_backend`;
- `simpleos_qemu_rv64_nested_simple_binary`;
- `simpleos_qemu_rv64_build_cc`;
- refreshed kernel/image candidate rows.

On the current Windows host the passing build path is:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1 -AttemptBuild -BuildDiskImage -BuildBackend cranelift -BuildCc C:\dev\install\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin\clang.exe
```

That path uses `src\compiler_rust\target\debug\simple.exe` as the nested Simple
binary, records `simpleos_qemu_rv64_build_status=pass`, produces
`build/os/simpleos_riscv64_smf_fs.elf`, compiles
`scripts/os/make_os_disk.c`, and records
`simpleos_qemu_rv64_disk_image_build_status=pass` for
`build/os/fat32-riscv64.img`. Disk-image builder compile/run diagnostics are
captured under `build/os/systest/qemu-riscv64-desktop/` and exposed as
`simpleos_qemu_rv64_disk_image_builder_compile_log_path` and
`simpleos_qemu_rv64_disk_image_builder_run_log_path`, with matching stdout path
rows for each process. The default LLVM backend remains blocked on this
host because the native backend is unavailable; host `gcc` is also not suitable
for the RISC-V native compile flags used by this build.

The same preflight also emits artifact-diagnostic rows so operators can see why
the desktop lane is still blocked:

- `simpleos_qemu_rv64_canonical_kernel_status` for
  `build/os/simpleos_riscv64_smf_fs.elf`;
- `simpleos_qemu_rv64_legacy_kernel_status` for smoke-only
  `build/os/simpleos_riscv64.elf`;
- `simpleos_qemu_rv64_fpga_kernel_status` for FPGA-only
  `build/os/simpleos_riscv64_fpga.elf`;
- `simpleos_qemu_rv64_canonical_image_status` for
  `build/os/fat32-riscv64.img`;
- `simpleos_qemu_rv64_storage_probe_image_status` for diagnostic-only
  `build/qemu-rv64-storage-probe.img`;
- `simpleos_qemu_rv64_kernel_candidate_status` and
  `simpleos_qemu_rv64_image_candidate_status` for the first existing candidate,
  or `none`.

Legacy or FPGA kernels are diagnostics only. They must not satisfy the QEMU
RV64 desktop service gate, which remains tied to the canonical SMF-FS kernel,
FAT32 image, and live serial/SSH/HTTP/GPU/WM probes.

QEMU service evidence is not the full Vulkan/WM completion gate. A live wrapper
must also feed `simpleos_multiconfig_live_required_evidence_keys()`, whose
aggregate status remains blocked until FPGA serial, Engine2D Vulkan, RenderDoc
artifact, structured WM comparison, and WM RenderDoc evidence also pass.
Use `scripts/check/check_simpleos_multiconfig_live_evidence.spl` as the
operator-facing aggregate status emitter; its default no-artifact run prints
`simpleos_multiconfig_live_status=blocked:qemu-service:blocked:missing-qemu-serial-console`.
When a live wrapper has QEMU, FPGA, Engine2D, RenderDoc, and WM rows, write the
six `simpleos_*_evidence_status=<status>` rows to a `key=value` file and pass it
with `--evidence <path>` or `SIMPLEOS_MULTICONFIG_EVIDENCE`.
The same file may instead contain raw QEMU service rows
(`simpleos_qemu_serial_console_status`, `simpleos_qemu_rv64_ssh_banner`,
`simpleos_qemu_rv64_http_status_code`, `simpleos_qemu_gpu_readback_status`,
`simpleos_qemu_wm_marker_status`); the aggregate checker derives
`simpleos_qemu_service_evidence_status` from them.

For the full Windows multi-config lane, use the combined wrapper:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-multiconfig-live-evidence.ps1
```

It runs the focused QEMU wrapper, FPGA serial wrapper, WM host-compare wrapper,
and Engine2D/RenderDoc normalizer in order. Intermediate files stay under
`build/simpleos_multiconfig_live_evidence/`, and the merged evidence file is
`build/simpleos_multiconfig_live_evidence/simpleos-multiconfig-live.env`. The
wrapper then invokes
`scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence` against
that merged file and exits with the aggregate checker status. A nonzero result
is expected until live QEMU serial/SSH/HTTP/GPU/WM, FPGA UART, Engine2D Vulkan,
RenderDoc `.rdc`, and host WM comparison evidence all pass.

When the merged file was produced by the Windows wrapper, the aggregate checker
also echoes `simpleos_multiconfig_windows_wrapper` plus the QEMU, FPGA, WM,
Engine2D, aggregate status, and aggregate exit-code rows. Use these diagnostics
to identify which child wrapper is still producing fail-closed evidence before
opening the full merged file.

Pass `-AttemptBuild` to the combined wrapper when the operator wants those QEMU
RV64 build rows included in
`build/simpleos_multiconfig_live_evidence/simpleos-multiconfig-live.env` and
echoed by the aggregate checker before the remaining FPGA, WM, and RenderDoc
gates are evaluated.

For the current Windows all-in-one desktop-service build plus live QEMU proof,
use:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-multiconfig-live-evidence.ps1 -BuildDesktopServiceKernel -RunLiveBoot -BootTimeoutSeconds 45 -BuildBackend cranelift -BuildCc C:\dev\install\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin\clang.exe
```

Expected current result is still nonzero, but QEMU service now passes. The
merged evidence records `simpleos_qemu_service_evidence_status=pass`, SSH
banner `SSH-2.0-SimpleOS_1.0`, HTTP `200`, QMP screendump/nonblank GPU
readback, and WM marker rows. The aggregate currently advances to
`blocked:fpga-serial:blocked:missing-fpga-uart-terminal`; Engine2D Vulkan,
RenderDoc, host-WM, and structured comparison evidence remain incomplete.

The FPGA RV64 profile remains UART serial-only in the same contract. Do not
reuse the QEMU SSH, HTTP, GPU, WM, Vulkan, or RenderDoc gates for FPGA until
board evidence expands that profile.

FPGA live wrappers must use `simpleos_fpga_serial_required_evidence_keys()`
instead. A passing FPGA serial row set names the `fpga-riscv64-serial` profile,
UART terminal status, serial device, serial boot marker, toolchain status, and
bitstream status, while SSH, HTTP, GPU, WM, Vulkan, and RenderDoc statuses stay
`blocked`.

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

The host-configuration matrix therefore checks `/db` on the HTTP listener's
8080 forward; it does not require a separate database port.

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

This routes to
`examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl` and
`build/os/simpleos_riscv64_display_smoke.elf`. One architecture display facade
owns the transitional runtime boundary and exposes dynamic mode, framebuffer,
stride, and checked present operations. The entry constructs
`FramebufferDriver`, compositor-owned surfaces, `DesktopShell`, and
`Engine2dWmFrameExecutor`; its completed `DrawIrComposition` is presented by a
VirtIO-GPU transfer plus flush. TODO 567 retains the pure-Simple DMA/queue
transport migration, so leaves do not acquire direct `rt_*` paths.

The source-ready interactive loop reuses `serial_init`/`serial_read_byte` and
the shared `uart_char_to_action`/`WmAction` mapping. It initializes serial only
after module initialization, polls without blocking, and for each changed
action rerenders through `DesktopShell`/`Engine2dWmFrameExecutor` before a
checked VirtIO-GPU present. It intentionally does not use WFI: the 16550 UART
IER is zero, so serial input cannot wake a sleeping CPU. The folded manual steps
are `Handle non-blocking UART window actions` and
`Present each changed frame through VirtIO-GPU`.

The wrapper keeps display-smoke evidence contract v2. Its default mode
requires ordered scanout,
first-frame, present, and desktop-ready markers with the same positive scene
revision, validates the dynamic PPM dimensions and stride, and accepts at least
four canonical desktop palette witnesses. Run its parser without QEMU via
`sh scripts/check/check-rv64-display-smoke-qmp-evidence.shs --self-test`.
The historical 2026-07-02 fixed-anchor report remains scanout-only evidence and
cannot pass contract v2. Until TODO 548 produces and boots a fresh pure-Simple
ELF, the canonical RV64 desktop is source-ready only; no live QEMU PASS is
claimed. TODO 565 and TODO 548 remain open for live proof.

The stricter RV64 WM/font/input contract v1 uses the same runner with a
distinct mode:

```bash
sh scripts/check/check-rv64-display-smoke-qmp-evidence.shs --self-test-wm-font-input
RV64_DISPLAY_SMOKE_BUILD=0 \
  scripts/check/check-rv64-display-smoke-qmp-evidence.shs --wm-font-input
```

It pins `/SYS/FONTS/NOTOSANS` to 1,708,408 bytes and SHA-256
`2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`,
requires the guest’s exact `rv64-font-evidence` marker for that identity and
the `shared-wm-draw-ir` route, rejects either font/input unavailable marker,
injects keyboard and pointer events through QMP VirtIO input, and requires
guest IRQ-to-WM-to-frame correlation. It captures the RV64-only
`right56,bottom48` RGB crop, rejects a one-byte-corrupted copy, and refuses PASS
until `RV64_WM_FONT_REGION_EXPECTED_SHA256` contains the genuine RV64 crop hash.
The x86_64 crop hash is never reused.

This strict mode is currently **BLOCKED**: the production RV64 entry does not
mount the selected font and does not consume VirtIO input. Its explicit
`rv64-font-evidence-unavailable` and `rv64-input-evidence-unavailable` markers
are blockers, not evidence. See
`doc/06_spec/03_system/os/wm/rv64_simpleos_wm_font_input_spec.md`.

## Host-GPU rendering and ProcessingIR

The canonical multi-ISA wrapper is:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --preflight
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test-qemu-accel
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test-runtime-provider
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test-metrics
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --validate-report build/simpleos_host_gpu_2d/report.env
```

For bounded ARM64 diagnosis only, a retained pure-Simple Phase-2 bootstrap
compiler may be selected with
`SIMPLEOS_HOST_GPU_ALLOW_BOOTSTRAP_COMPILER_DIAGNOSTIC=1`. This opt-in requires
an explicit canonical, regular, non-symlink `SIMPLE_BIN`, `aarch64` as the sole
guest ISA, and a distinct build directory containing `diag` or `diagnostic`.
It runs the real native frontend smoke and rejects Rust/seed delegation markers.
Its receipts are always
`evidence_class=diagnostic-phase2-non-attested`; they cannot become a canonical
production PASS or satisfy report validation.

Run `--preflight` first. It does not compile or boot SimpleOS. For each ISA it
records the selected accelerator, default VirtIO-GPU 2D availability,
`ivshmem-plain`, and accelerated GL/rutabaga device availability. A same-ISA
guest selects KVM on Linux, HVF on macOS, or WHPX on Windows only when the
selected QEMU binary advertises it; cross-ISA rows use TCG. Native AArch64 uses
`-cpu host`, while AArch64 TCG uses `-cpu cortex-a72`.

Interpret the fields strictly:

- `virtio_gpu_2d=yes` proves a scanout/presentation device only;
- `ivshmem_plain=yes` is required by the supported host-offload transport;
- `gl_or_rutabaga=yes` is informational and does not prove Venus, Metal,
  Vulkan, or device-origin readback;
- `status=ready` permits the bounded build/boot gate to start, but is not a GPU
  PASS.

On Linux, the live wrapper admits the Vulkan/CUDA runtime archive only after
checking both its Cargo feature fingerprint and its exported daemon-provider
closure. The archive must define the retained crypto and frame-clock owners
(`rt_tls13_sha256`, `rt_sleep_nanos`) plus the Vulkan initialization, raw SPIR-V
compile, compute-pipeline, and provider availability/device-count owners. A
default archive that fails this check is
rebuilt once, without clearing its Cargo cache, through the canonical
`simple-runtime` target and checked again before native daemon linking. The
same admitted `libsimple_runtime.a` is supplied explicitly through
`SIMPLE_LINK_OBJECTS`; `core-c-bootstrap` does not infer Rust providers from
`--runtime-path`. An explicit incomplete archive fails closed as
`runtime-provider-closure-missing`; the linker is never used as the provider
discovery mechanism. `--self-test-runtime-provider` compiles and links a
complete fixture archive, then proves that both archive admission and consumer
linking reject a missing-provider fixture.

The 2026-07-26 Apple Silicon preflight is retained in
`doc/09_report/simpleos_qemu_macos_gpu_preflight_2026-07-26.md`. Homebrew QEMU
10.2.2 selects HVF for AArch64 and TCG for x86_64/RISC-V, but its three
system-emulator binaries expose neither `ivshmem-plain` nor accelerated
GL/rutabaga devices. Do not start the live gate with that deployment. Install
or build a QEMU deployment that actually reports `ivshmem_plain=yes`, then run
the wrapper again; package presence or configure flags are not substitutes for
the executed preflight.

Before building a guest, both compiler selectors use the same private
candidate-admission contract. Shell `candidate_frontend_smoke` and
`simple_binary_is_valid` live in
`scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs`, which is
sourced by both `bootstrap-from-scratch.sh` and the QEMU wrapper; `_QemuRunner`
keeps the equivalent pure-Simple `_candidate_frontend_smoke`. Each self-pins `SIMPLE_BINARY`, `SIMPLE_BIN`,
`SIMPLE_BOOTSTRAP_DRIVER`, and `SIMPLE_FRONTEND_DELEGATE` to the candidate;
sets `SIMPLE_FRONTEND_DELEGATED=1`, `SIMPLE_NO_STUB_FALLBACK=1`, and
`SIMPLE_LIB=$ROOT_DIR/src`; and neutralizes inherited worker/bootstrap modes
with `SIMPLE_EXECUTION_MODE=''`, `SIMPLE_NATIVE_BUILD_FORCE_WORKER=0`, and
`SIMPLE_BOOTSTRAP=0`. It then native-builds the checked-in
`scripts/check/cert/redeploy_gate/fixtures/p2_add.spl` with Cranelift,
core-C-bootstrap, entry closure, and one-binary mode. The build has 60 seconds;
the resulting program has 5 seconds and must exit zero with stdout exactly
`5`. The shared admission subshell owns trap-0 cleanup; the runner uses bounded `mktemp`
scratch and requires recursive cleanup before acceptance. The invalid-mode
probe goes through runner `_run_candidate_admission_pinned`, so a sibling seed
cannot answer for the candidate.

The admitted candidate is pinned again for the authoritative guest build.
`build_os_with_backend` first installs target-specific settings through
`_apply_build_env`, then calls `_run_candidate_pinned`; those inherited target
settings remain intact while compiler/delegate identity and no-stub behavior
are pinned. The real guest native-build therefore cannot re-enter a sibling or
seed delegate after admission.
If the candidate is a symlink such as `bin/simple`, shared CLI
`_cli_is_current_exe` first resolves it through existing
`_cli_resolve_symlink`. Authoritative worker delegation then recognizes the
admitted executable rather than redirecting to a sibling. The focused
`test/01_unit/app/io/cli_argv0_resolution_spec.spl` source contract adds no
`rt_*` alias.

Do not use `check test/05_perf/io_parity/startup_simple.spl` as admission
evidence. `run_check` always appends whole-tree repository hygiene, so
unrelated tracked-policy failures can reject a correct frontend, and its Git
subguards are not authoritative in a jj workspace with `.jj` and no `.git`.
Bootstrap retains its focused `check src/app/cli/bootstrap_main.spl`, but no
longer uses the whole-tree check for candidate admission. The wrapper self-test
and shared-shell syntax check pass; `_QemuRunner` source parity is present. TODO
548 remains open until a current-source pure-Simple CLI executes the runner
gate; no live compiler, QEMU, or GPU PASS is implied. Native-Windows
child-environment, platform-neutral unique-temp, and argv-preserving timeout
ownership are tracked by TODO 573. All five split `_QemuRunner` modules now use
shared I/O/process/time owners; `runner_targets` reads its baseline without
shell `cat`. TODO 574 retains overflow-safe monotonic elapsed timing.

Do not replace `process_ops` with the Rust SFFI timeout wrapper alone. It is not
available in every hosted runtime provider, its Unix timeout child lacks group
setup for orphan cleanup, and Windows lacks process-tree cleanup. TODO 573 must
prove provider-complete argv/output/deadline/orphan behavior, then child-env
isolation and atomic host-temp creation, before removing POSIX `env`/`mktemp`.

Candidate admission does not make focused SSpec execution pure-Simple.
Current `simple test` reaches `rt_cli_run_tests`; directly entering the
pure-Simple orchestrator still reaches the Rust `rt_cli_run_file` interpreter.
TODO 572 owns the dedicated result-bearing pure-Simple compiler/test-runner
path. Until it is implemented, record focused SSpec verification as blocked;
never set `SIMPLE_BOOTSTRAP_DRIVER` to a Rust seed as a workaround.

It builds `simpleos-host-gpu-x86_64`, `simpleos-host-gpu-aarch64`, and
`simpleos-host-gpu-riscv64` through `_QemuRunner`, starts the strict host
daemon over one bounded ivshmem region per row, and requires the existing
64x48 raw-render and full-frame IMAGE regression, a separate exact 1280x720
two-RECT Draw IR readback, and independent ProcessingIR device-readback probe.
The AArch64 row has a second mandatory phase: after that probe passes, the
wrapper boots `arm64-desktop-engine2d` while retaining the same daemon, shared
memory file, and RSS metrics file. Each QEMU phase is sampled concurrently with
the daemon, and the daemon, QEMU, and combined maxima carry across both boots.
The exact fixture compares all 921,600 returned pixels with its positional CPU
oracle and requires checksum 1417723768, 633,600 background pixels, 288,000
foreground pixels, and zero mismatches. The production phase does not replace
or weaken either probe. Its ready generation must continue the probe's final
ProcessingIR generation according to the shared Metal, DirectX, then Vulkan
negotiation order, proving both boots used one daemon session rather than two
independent valid logs.

After the full positional oracle, the probe submits exactly 20 additional
identical 1280x720 Draw IR generations. The serial log must contain samples
1..20 with consecutive generation/frame IDs, positive elapsed time, matching
run/backend/device identity/dimensions/output bytes/checksum, and zero
mismatches. The wrapper computes nearest-rank p95 at rank 19. It enforces the
16,700 us limit only when the same row's exact retained QEMU argv marker proves
matching KVM/HVF/WHPX acceleration; every TCG row is correctness-only. The
source, parser, cached validator, and self-test are ready, but fresh current-host
native/TCG execution remains required. Twenty extra samples may expose a real
wall-time need; set `SIMPLEOS_HOST_GPU_QEMU_TIMEOUT` for that run if necessary,
without changing the checked-in default.

The second QEMU argument vector must have this exact token shape (with the
row-owned shared-memory path substituted for `<row-shm>`):

```text
-machine virt -accel <tcg|native-accelerator> -cpu <cortex-a72|host> -m 512M
-kernel build/os/simpleos_arm64_desktop_engine2d.elf
-nographic
-device ramfb
-device virtio-net-pci
-object memory-backend-file,id=hostgpu,share=on,mem-path=<row-shm>,size=8M
-device ivshmem-plain,memdev=hostgpu
```

The CPU/accelerator pair is exact: TCG uses `cortex-a72`; a validated native
KVM/HVF/WHPX row uses `host`. The production boot must retain the probe's pair.

A production pass requires the serial
sequence `[wm-frame] host-gpu-ready` -> `[wm-frame] host-gpu-presented` ->
`[desktop-gui] first-frame-rendered` ->
`[desktop-gui-arm64] desktop-ready`, together with successful RAMFB
configuration. The selected backend must match the host contract; the
presented run must equal the ready generation; the presented generation and
frame must be equal and exactly one newer; its checksum must be positive; and
the two desktop revisions must be equal and positive.

Linux Vulkan rendering and the native CUDA ProcessingIR executor are
implemented with Vulkan ProcessingIR fallback. On a host offering both CUDA
and Vulkan, a CUDA-preferred receipt does not exercise or close the Vulkan
ProcessingIR capability row. The daemon owner now accepts an explicit
`--processing-backend=vulkan` filter, and the canonical wrapper applies it
without changing the default CUDA preference:

```sh
SIMPLEOS_HOST_GPU_PROCESSING_BACKEND=vulkan \
  sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs
```

After accepting a current pure-Simple compiler, the Linux wrapper directly
builds the canonical guest entries with that compiler and validates the
architecture-tagged host-runtime archive and its Cargo fingerprint. If missing,
it builds only that lane-owned SFFI provider with:

```sh
CARGO_TARGET_DIR="$PWD/build/simpleos_gpu_host/$(uname -m)-vulkan-cuda-runtime-target" \
  cargo build --locked --manifest-path src/compiler_rust/Cargo.toml \
  --package simple-runtime --lib --profile bootstrap --features vulkan,cuda
```

The fingerprint proves these compile features; live negotiation and
device-readback receipts still prove hardware execution. A user-supplied
`SIMPLEOS_HOST_GPU_RUNTIME_PATH` is never deleted or rebuilt and fails closed
when its archive/fingerprint is invalid. This host SFFI build does not permit
using the Rust compiler seed for Simple checks, guest builds, or execution.

The forced lane must negotiate processing mask `1`, emit a single
`HOST_GPU_DAEMON_SELECTOR processing_backend=vulkan` receipt, and retain exact
device readback before TODO 550 can close. TODO 570 retains the
correlated preference classification; refreshed cross-ISA CUDA receipts are
also still required. macOS Metal Draw IR backend execution is implemented, but
the 2026-07-27 prepared-host audit found that the QEMU daemon still cannot be
built through the supported narrow native lane: importing Draw IR pulls the
monolithic `Engine2D` closure and every backend provider. It therefore remains
`blocked`, not accelerated, until the shared internal render/readback target
described below produces a Metal-only daemon and a fresh receipt.
Metal ProcessingIR FillU32 is implemented through a dedicated checked MSL
kernel and device readback, but likewise needs a prepared-host receipt. Windows
DirectX/CUDA rows remain `unsupported` evidence until a prepared host produces
fresh receipts; a bounded native D3D11 owner is implemented, but its API name
alone is not proof. The host Draw IR executor retains the parent Vulkan or Metal
session for bounded smaller WM surfaces, requires child device readback, and
applies canonical embedding opacity through checked native parent src-over.
The additive `arm64-desktop-engine2d` scenario supplies the canonical
RAMFB/`DesktopShell` build target, and the wrapper source now defines the
correlated production-frame gate above. On 2026-07-15 diagnostic full-bootstrap
Stage3 hash `ff192f9d...` passed admission. The runtime root fix lets section GC
discard dead optional backends, and the tagged Vulkan/CUDA daemon now links
without core-C ABI mixing. The bounded AArch64 run builds, boots, maps ivshmem,
and reports generation zero, zero negotiation attempts, and reason 7 because
the daemon does not enter the HELLO service loop. Reject the x86 diagnostic
that admitted all of `rt_extras.c`: it duplicates strong providers already in
`baremetal_stubs.c`, and `-z muldefs` makes ownership order-dependent. TODO577
owns daemon HELLO, TODO578 owns the x86 minimal runtime split, and TODO537 owns
RV64. Final source removes the rejected admission and still needs one
source-matched rebuild under TODO548. No live GPU receipt is claimed.
Cached reports are accepted only through `--validate-report`: an overall status
cannot promote the lane unless all nine host/ISA rows are well-formed and a
passing active host carries three existing serial logs with exact correlated
render, Draw IR, 1280x720 fixture, and ProcessingIR receipts. Each passing row
also carries one daemon performance receipt correlated by
ISA/backend/generation/run/frame.
The validator requires positive CPU/device microseconds, requires device time
to match the guest receipt, and independently labels the existing
FillU32(256, 7) request `preferred` only at 1.5x or greater speedup; a correct
slower request is `available-not-preferred`. Missing, duplicate, stale, zero,
or dishonest classification fails closed. A passing active AArch64 row must
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
the latency or 256 MiB combined QEMU-plus-daemon RSS targets. TODO 569 remains
open until prepared native rows execute the now-source-ready 1280x720 fixture;
TODO 570 remains open until prepared native rows execute the now-source-ready
ProcessingIR preference contract.

### External-host postponement and resume contract

Prepared Windows DirectX, macOS Metal, and NVIDIA CUDA execution evidence is
postponed only when the required native capability is unavailable; postponement
is not completion. Current-host CUDA device readback and UUID/multi-GPU checks
remain active and do not wait for the Simple compiler, while their QEMU receipts
do. The authoritative host prerequisites, commands, retained artifacts,
existing TODO ownership, and remaining local work are in
`doc/03_plan/agent_tasks/simpleos_qemu_host_gpu_external_host_evidence.md`
(TLDR alongside). Do not create replacement TODOs for these rows.

The postponement applies only to non-current prepared-host portions of TODO
563, TODO 569, and TODO 570. Their current Linux Vulkan measurements remain
active. Resume an external row only on its prepared native host and only after
`simple_binary_is_valid` accepts the selected pure-Simple compiler. Source
presence, API names, translation or emulation, screenshots, cached reports,
synthetic handles, and CPU mirrors cannot promote a row. A native PASS still
requires submission, terminal completion, device-origin readback, stable
device identity, exact CPU-oracle parity, correlated generation/run/frame IDs,
and final normal/highest-capability review.

TODO 566 follows the same split: hardware-independent source/parser/self-test
work and the current Linux native row remain active, while unavailable
Windows/macOS native timing rows are postponed. Measure one guest-observed
interval from device initialization through every rejected or timed-out Metal,
DirectX, and Vulkan attempt to backend selection or CPU fallback. Daemon HELLO
`elapsed_us` and cross-ISA TCG are correctness evidence only and cannot close
the inclusive 500,000 us native target. Report only `current-host scope
complete`; keep the umbrella host-GPU lane incomplete while any required
prepared-host row remains postponed.

Accelerator applicability comes from the retained executed QEMU argv, not from
host/guest ISA equality alone. The wrapper uses KVM on Linux, HVF on macOS, or
WHPX on Windows only when that accelerator is available, advertised by the
selected QEMU binary, and the guest ISA matches the host; otherwise it records
TCG and treats the row as correctness-only. Production negotiation evidence
also requires exactly one scoped `HOST_GPU_MAP_OK` before the first attempt or
final decision. Two valid clock samples in the same microsecond are recorded as
1 us so zero remains an invalid interval.

The 20-sample warm render/readback p95 contract is source/parser/self-test
ready. TODO 563 remains open for fresh current-host native and TCG execution
and fresh combined QEMU-plus-daemon RSS evidence; source readiness does not
satisfy NFR-003 or NFR-005.

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

### Direct guest GPU passthrough

Direct guest Vulkan/CUDA access is distinct from the supported ivshmem
host-daemon offload path. Inspect it without changing device ownership:

```sh
sh scripts/check/check-simpleos-qemu-guest-gpu-passthrough.shs --self-test
sh scripts/check/check-simpleos-qemu-guest-gpu-passthrough.shs --preflight
```

The preflight reports IOMMU groups, display-device driver ownership, QEMU
`vfio-pci` and `virtio-gpu-gl` status, selected-device and whole-IOMMU-group
readiness, validated SimpleOS guest device-readback evidence, and the separate
ivshmem checker path. It never loads
modules or unbinds/rebinds a PCI device. A live VFIO attempt requires an
explicitly selected spare GPU or approved maintenance window, every function in
its IOMMU group, recovery console access, and a matching SimpleOS guest driver.
The checker executes bounded probes only for root-owned, non-group/world-writable
QEMU binaries whose trusted parent directories are under `/usr/bin` or
`/usr/local/bin`. It deliberately rejects every purported
guest receipt until a canonical SimpleOS guest producer exists; caller-authored
text and hashes are not execution provenance.

The dated 2026-07-15 Linux preflight found IOMMU and QEMU `vfio-pci`, both
NVIDIA GPUs bound to host drivers, a broken `virtio-gpu-gl` module dependency,
and no validated SimpleOS guest Vulkan/CUDA device-readback evidence. The result
is therefore `unavailable`; the separately verified ivshmem design remains the
viable implementation path, while this checker reports only its presence.
TODO575 owns future direct-passthrough work and cannot be closed by host Vulkan,
CUDA, QEMU flags, or host-daemon receipts.

### Cross-host and native-board GPU extension

The shared architecture and nonduplicating execution plan are:

- `doc/04_architecture/simpleos_qemu_host_gpu_2d.md`;
- `doc/05_design/simpleos_qemu_host_gpu_2d.md`;
- `doc/03_plan/agent_tasks/simpleos_cross_host_qemu_board_gpu_2d_parity.md`.

Linux, macOS, and Windows QEMU reuse the existing host-GPU protocol, fixture,
receipt, and CPU SIMD oracle. Physical boards reuse the same artifact and
evidence ladder through a board adapter; they do not create another Simple 2D
or Draw IR interface.

For macOS, resume in this order:

1. implement the internal Draw IR render/readback target from
   FR-GPU-QEMU-0001, with normal Engine2D and Metal-only host adapters;
2. run the dependency check and reject any daemon closure retaining unused
   Vulkan/OpenGL/Intel/WebGPU provider symbols;
3. native-build the daemon with the supported pure-Simple/core-C lane;
4. run `sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs` with the admitted
   compiler and retain its exact HVF argv;
5. accept only positive Metal identity/handle, same-frame device readback,
   twenty warm samples, and zero CPU/SIMD pixel mismatches.

Do not use a cached daemon, the Rust bootstrap seed, a CPU mirror, a synthetic
handle, Cocoa presentation, or a Metal API name as native evidence.

Default VirtIO-GPU 2D is presentation-only. Current upstream accelerated
virgl/Venus/rutabaga host requirements are Linux-scoped. macOS Venus remains
unsupported by current upstream Venus requirements; UTM Venus/MoltenVK is a
separate pinned experiment. Windows accelerated upstream virtio-gpu remains
blocked pending a maintained port. Never infer GPU readiness from HVF, KVM,
WHPX, SDL/GTK/Cocoa display, or QMP output.

Linux, Windows, UNO Q, VisionFive 2, and UP Squared execution unavailable in
the current environment is postponed under
`doc/08_tracking/todo/simpleos_qemu_host_gpu_postponed_2026-07-15.md`.
Every row remains required and manual-visible. Resume only with the
prerequisites, exact commands, artifact paths, owner, and final reviewer listed
in the extension plan.
## Restart12 toolchain deployment row (2026-08-14)

The x86_64 production-desktop/toolchain row remains BLOCKED. Its future SSpec
is `test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl` with
the mirrored operator manual under `doc/06_spec/03_system/os/`. It must fail
closed when the admitted image, OVMF/GRUB desktop receipt, framebuffer proof,
or guest compile/run receipt is absent; it may never `skip()` or green on a
readiness-only/fixed-command path. Use the frozen helper/step vocabulary and
same-run evidence contract in
`doc/03_plan/os/simpleos/hw_qemu/x86_64_native_hello_world_plan.md`.
