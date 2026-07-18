# SimpleOS Multi-Config Vulkan WM Contract

**Source:** `test/01_unit/os/simpleos_config_matrix_spec.spl`
**Plan:** `doc/03_plan/os/simpleos_multiconfig_vulkan_wm_plan.md`
**Status:** Manual mirror because the current Windows docgen runtime emits a
stub with `trim_end` runtime errors for this spec.

## Overview

This scenario verifies the static, non-hardware contract for the SimpleOS
multi-config hardening lane. QEMU RV64 is the desktop, service, GPU, WM,
Vulkan, and RenderDoc profile. FPGA RV64 remains UART serial-only until
hardware evidence expands it.

Completion still requires live QEMU, GPU readback, Vulkan, RenderDoc `.rdc`,
and host-WM comparison evidence. This spec only proves the contract is
fail-closed and machine-checkable.

## Scenario: QEMU RV64 Desktop Profile

1. Load the QEMU RV64 desktop profile.
2. Confirm the profile name is `qemu-riscv64-desktop`.
3. Confirm the architecture is `riscv64`.
4. Confirm SSH is exposed through `127.0.0.1:2222`.
5. Confirm HTTP/webserver is exposed through `127.0.0.1:8080`.
6. Confirm every required QEMU capability reports `ready`.

Required capabilities:

- serial terminal
- SSH
- HTTP
- GPU
- framebuffer
- WM
- Simple2D over Engine2D
- Vulkan
- RenderDoc
- host WM comparison

## Scenario: FPGA RV64 Serial-Only Profile

1. Load the FPGA RV64 serial profile.
2. Confirm the profile name is `fpga-riscv64-serial`.
3. Confirm the architecture is `riscv64`.
4. Confirm the terminal kind is `uart-serial`.
5. Confirm the FPGA serial entry path is
   `examples/09_embedded/simple_os/arch/riscv64/fpga_serial_entry.spl`.
6. Confirm the FPGA serial kernel path is `build/os/simpleos_riscv64_fpga.elf`.
7. Confirm the canonical FPGA boot marker is
   `SIMPLEOS_FPGA_RISCV64_SERIAL_BOOT`.
8. Confirm serial terminal support is enabled.
9. Confirm all non-serial desktop capabilities return
   `blocked:fpga-riscv64-currently-uart-serial-only:<capability>`.

Blocked FPGA capabilities:

- SSH
- HTTP
- GPU
- framebuffer
- WM
- Simple2D over Engine2D
- Vulkan
- RenderDoc
- host WM comparison

## Scenario: FPGA RV64 UART Serial Evidence

1. Read `simpleos_fpga_serial_required_evidence_keys()`.
2. Confirm the contract requires the `fpga-riscv64-serial` board profile.
3. Confirm the contract requires the expected FPGA serial entry.
4. Confirm the contract requires the expected FPGA serial kernel path.
5. Confirm the contract requires UART terminal status.
6. Confirm the contract requires a serial device name.
7. Confirm the contract requires a serial boot marker.
8. Confirm the contract requires toolchain and bitstream status.
9. Confirm the contract requires SSH, HTTP, GPU, WM, Vulkan, and RenderDoc
   statuses to remain `blocked`.
10. Confirm a fully populated serial-only evidence record reports `pass`.
11. Confirm missing UART terminal evidence blocks completion.
12. Confirm mistakenly enabled SSH blocks completion.
13. Confirm mistakenly enabled GPU blocks completion.

This scenario is a non-hardware evidence contract. It preserves the current
FPGA scope as UART serial-only and requires any future board lane to prove UART
boot before expanding the capability matrix.

## Scenario: QEMU Launch Arguments

1. Read `qemu_riscv64_desktop_qemu_args()`.
2. Confirm the artifact directory is
   `build/os/systest/qemu-riscv64-desktop`.
3. Confirm launch argument validation returns `ready`.
4. Confirm `os.qemu_systest_contract.riscv64_desktop_qemu_args_status()`
   also returns `ready`.
5. Confirm the QEMU system-test desktop alias includes `virtio-gpu-pci,disable-modern=on,disable-legacy=off`.
6. Confirm QEMU user networking forwards `tcp::2222-:22` and
   `tcp::8080-:8080`.
7. Confirm `virtio-net-pci,netdev=rvnet` is present.
8. Confirm `virtio-gpu-pci,disable-modern=on,disable-legacy=off` is present.
9. Confirm headless display `none` is present.
10. Confirm QMP `tcp:127.0.0.1:4444,server,nowait` is present.

## Scenario: QEMU Service Evidence

1. Read `simpleos_qemu_service_required_evidence_keys()`.
2. Confirm the contract requires serial console status.
3. Confirm the contract requires an SSH banner and SSH probe status.
4. Confirm the contract requires HTTP status code and HTTP probe status.
5. Confirm the contract requires QEMU GPU readback status.
6. Confirm the contract requires a QEMU WM marker status.
7. Confirm a fully populated evidence record reports `pass`.
8. Confirm missing SSH banner blocks completion.
9. Confirm missing GPU readback blocks completion.

This scenario is still a contract check. It defines the live rows that a QEMU
wrapper must emit; it does not claim that this Windows run booted QEMU or
opened SSH, HTTP, GPU, or WM sessions.

## Scenario: Structured WM Comparison Evidence

1. Read `simpleos_wm_structured_compare_required_evidence_keys()`.
2. Confirm the contract requires QEMU and host scene names.
3. Confirm the contract requires QEMU and host window counts.
4. Confirm the contract requires QEMU and host focus IDs.
5. Confirm the contract requires QEMU and host titlebar/taskbar status.
6. Confirm the contract requires RenderDoc log comparison status.
7. Confirm the contract requires ARGB diff status and mismatch count.
8. Confirm a fully populated evidence record reports `pass`.
9. Confirm scene mismatch blocks completion.
10. Confirm missing RenderDoc log comparison blocks completion.
11. Confirm nonzero ARGB mismatches block completion.

This scenario defines the structured comparison rows that a QEMU SimpleOS WM
versus host WM wrapper must emit. It intentionally treats bitmap parity as
insufficient unless the scene, WM state, RenderDoc log comparison, and ARGB
diff metadata also agree.

The Windows WM wrapper keeps WM scene identity separate from the RenderDoc
Engine2D scene: `simpleos_wm_compare_scene` defaults to
`simpleos-desktop-four-windows`, while `simpleos_wm_renderdoc_scene` defaults
to `vulkan-engine2d`.

## Scenario: Simple2D Over Engine2D Vulkan Evidence

1. Read `simpleos_engine2d_vulkan_required_evidence_keys()`.
2. Confirm the contract requires the Engine2D runtime backend.
3. Confirm the contract requires the `vulkan-engine2d` scene.
4. Confirm the contract requires Simple2D command evidence.
5. Confirm the contract requires a Vulkan device name.
6. Confirm the contract requires viewport width and height.
7. Confirm the contract requires a readback checksum.
8. Confirm the contract requires nonblank readback status.
9. Confirm the contract requires QEMU GPU readback status.
10. Confirm a fully populated evidence record reports `pass`.
11. Confirm CPU fallback blocks Vulkan completion.
12. Confirm missing checksum blocks readback completion.
13. Confirm missing QEMU GPU readback blocks completion.

This scenario is a non-hardware evidence contract. It requires the future live
wrapper to prove Simple2D commands rendered through Engine2D on Vulkan and
returned nonblank QEMU GPU readback before the lane can claim acceleration.

## Scenario: QEMU SimpleOS Engine2D Vulkan Bridge Path

1. Read `simpleos_engine2d_vulkan_bridge_required_keys()`.
2. Confirm the bridge profile is `qemu-riscv64-desktop`.
3. Confirm the QEMU drawing backend is `virtio_gpu`.
4. Confirm the Engine2D processing backend is `vulkan`.
5. Confirm the QEMU GPU device is `virtio-gpu-pci,disable-modern=on,disable-legacy=off`.
6. Confirm the scene is `vulkan-engine2d`.
7. Confirm Simple2D commands enter Engine2D through `draw_ir-to-engine2d`.
8. Confirm Engine2D device readback is required.
9. Confirm QEMU QMP screendump readback is required.
10. Confirm RenderDoc capture mode is `capture-simple`.
11. Confirm the WM comparison scene is `simpleos-desktop-four-windows`.
12. Confirm CPU processing fallback blocks the bridge plan.
13. Confirm a missing QMP screendump requirement blocks the bridge plan.

This scenario is the implementation-facing target for live wrappers. It does
not prove QEMU booted or Vulkan rendered; it prevents the SimpleOS path from
passing through a CPU fallback, screenshot-only readback, or non-Simple
RenderDoc capture mode. The Windows Engine2D/RenderDoc normalizer emits these
bridge rows, and the aggregate checker prints
`simpleos_engine2d_vulkan_bridge_status` as a diagnostic beside the six live
completion gates.

When a QEMU screendump PPM exists, the normalizer also records
`simpleos_qemu_gpu_readback_width`, `simpleos_qemu_gpu_readback_height`, and
`simpleos_qemu_gpu_readback_dimensions_status`. These are diagnostic viewport
rows and cannot turn a missing Engine2D Vulkan backend into a pass.

The Windows WM host-compare wrapper can also run with `-AttemptHostWmCapture`.
That option invokes the existing hosted-WM capture entrypoint and records
attempt/status/exit/log rows. These rows expose host capture failures without
changing the structured-compare pass criteria.

## Scenario: RenderDoc Artifact Evidence

1. Read `simpleos_renderdoc_artifact_required_evidence_keys()`.
2. Confirm the contract requires RenderDoc capture mode.
3. Confirm the contract requires a SimpleOS `.rdc` path.
4. Confirm the contract requires `.rdc` magic `RDOC`.
5. Confirm the contract requires `.rdc` payload size greater than the header.
6. Confirm the contract requires a capture log path and pass status.
7. Confirm the contract requires Vulkan runtime backend and
   `vulkan-engine2d` scene.
8. Confirm the contract requires the RenderDoc helper to pass.
9. Confirm the contract requires QEMU WM and host WM RenderDoc log paths.
10. Confirm a fully populated evidence record reports `pass`.
11. Confirm `capture-html` blocks this SimpleOS RenderDoc lane.
12. Confirm missing `RDOC` magic blocks completion.
13. Confirm a header-only `.rdc` blocks completion.
14. Confirm missing host WM RenderDoc log blocks completion.

This scenario separates artifact validation from visual comparison. A SimpleOS
RenderDoc pass requires `scripts/tool/renderdoc-evidence.shs capture-simple`,
an `.rdc` file with `RDOC` magic and payload bytes, a passing capture log,
Vulkan Engine2D metadata, and both QEMU and host WM logs.

## Scenario: RenderDoc And WM Evidence

1. Read `simpleos_wm_renderdoc_required_evidence_keys()`.
2. Confirm the contract requires SimpleOS `.rdc` `RDOC` magic.
3. Confirm the contract requires the emitted Simple RenderDoc runtime backend
   row to be `vulkan`.
4. Confirm the contract requires the emitted Simple RenderDoc scene row to be
   `vulkan-engine2d`.
5. Confirm the contract requires Simple2D readback.
6. Confirm the contract requires QEMU GPU readback.
7. Confirm the contract requires QEMU WM evidence.
8. Confirm the contract requires host WM evidence.
9. Confirm the contract requires structured QEMU-vs-host WM comparison.
10. Confirm a fully populated evidence record reports `pass`.
11. Confirm missing `RDOC` magic blocks completion.
12. Confirm CPU fallback blocks Vulkan completion.

## Scenario: Aggregate Live Evidence Gate

1. Read `simpleos_multiconfig_live_required_evidence_keys()`.
2. Confirm the aggregate requires QEMU service evidence status.
3. Confirm the aggregate requires FPGA serial evidence status.
4. Confirm the aggregate requires Engine2D Vulkan evidence status.
5. Confirm the aggregate requires RenderDoc artifact evidence status.
6. Confirm the aggregate requires structured WM comparison evidence status.
7. Confirm the aggregate requires WM RenderDoc evidence status.
8. Confirm a fully populated aggregate evidence record reports `pass`.
9. Confirm missing QEMU service evidence identifies the QEMU service lane.
10. Confirm missing FPGA serial evidence identifies the FPGA serial lane.
11. Confirm missing RenderDoc artifact evidence identifies the RenderDoc lane.

This scenario is the top-level non-hardware completion contract. It does not
prove live QEMU, FPGA, Vulkan, RenderDoc, or WM comparison evidence exists;
instead, it defines the exact aggregate status a future live wrapper must
produce before the full lane can claim completion.

## Scenario: Default Live Evidence Is Blocked

1. Construct `default_blocked_simpleos_multiconfig_live_evidence()`.
2. Confirm the QEMU service row reports
   `blocked:missing-qemu-serial-console`.
3. Confirm the FPGA row reports `blocked:missing-fpga-uart-terminal`.
4. Confirm the Engine2D Vulkan row reports
   `blocked:missing-engine2d-vulkan-backend`.
5. Confirm the RenderDoc artifact row reports
   `blocked:missing-renderdoc-capture-simple-mode`.
6. Confirm the structured WM comparison row reports
   `blocked:missing-qemu-wm-scene`.
7. Confirm the WM RenderDoc row reports `blocked:missing-simple-rdoc-magic`.
8. Confirm the aggregate status reports
   `blocked:qemu-service:blocked:missing-qemu-serial-console`.

The runnable status emitter is
`scripts/check/check_simpleos_multiconfig_live_evidence.spl`. It prints these
same `simpleos_*` rows for operators and exits nonzero until real live evidence
replaces the default missing-evidence records.

## Scenario: Live Evidence Status Rows

1. Construct aggregate live evidence from six explicit status rows.
2. Confirm six `pass` rows produce aggregate `pass`.
3. Confirm a QEMU service row such as `blocked:missing-qemu-http-200` reports
   `blocked:qemu-service:blocked:missing-qemu-http-200`.
4. Confirm a structured WM row such as `blocked:wm-argb-mismatch` reports
   `blocked:wm-structured-compare:blocked:wm-argb-mismatch`.

This scenario is the pure contract behind the checker `--evidence <path>` mode.
Future live wrappers should write the six aggregate `key=value` rows named by
`simpleos_multiconfig_live_required_evidence_keys()` into that file.
The operator output also prints
`simpleos_renderdoc_artifact_required_evidence_keys` and
`simpleos_wm_renderdoc_required_evidence_keys` so RDOC status and WM RenderDoc
requirements are visible during blocked runs.
The checker also accepts raw per-lane rows such as
`simpleos_qemu_rv64_http_status_code=200`,
`simpleos_engine2d_runtime_backend=vulkan`,
`simpleos_renderdoc_rdc_magic=RDOC`,
`simpleos_renderdoc_rdc_magic_status=pass`, and
`simpleos_wm_argb_mismatch_count=0`; it derives the six aggregate statuses from
those rows and keeps missing rows blocked. Raw `RDOC` magic alone is not enough;
the explicit magic-status row must pass too.

On Windows, the combined operator wrapper is
`scripts/check/check-simpleos-multiconfig-live-evidence.ps1`. It chains the
focused QEMU, FPGA, WM compare, and Engine2D/RenderDoc wrappers into
`build/simpleos_multiconfig_live_evidence/simpleos-multiconfig-live.env`, then
runs this aggregate checker against the merged raw-row file. The current host
result is expected to exit nonzero until live QEMU artifacts, FPGA serial
evidence, Vulkan readback, RenderDoc `.rdc`, and WM comparison artifacts exist.
The aggregate checker echoes the Windows wrapper name and child exit-code rows
when the merged evidence file contains them, so the operator can see which
wrapper is still blocked without manually scanning the file first.
With `-AttemptBuild`, the QEMU wrapper first attempts
`src\compiler_rust\target\debug\simple.exe os build --arch=riscv64`, writes
`build/os/systest/qemu-riscv64-desktop/rv64-build.log`, and adds build status
rows. Current Windows passing build evidence uses `-BuildBackend cranelift`
with
`-BuildCc C:\dev\install\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin\clang.exe`,
records `simpleos_qemu_rv64_build_status=pass`, identifies
`src\compiler_rust\target\debug\simple.exe` as the nested Simple binary, and
produces `build/os/simpleos_riscv64_smf_fs.elf`. With `-BuildDiskImage`, the
wrapper compiles `scripts/os/make_os_disk.c` and records
`simpleos_qemu_rv64_disk_image_build_status=pass` for
`build/os/fat32-riscv64.img`.
With `-BuildDesktopServiceKernel -RunLiveBoot`, current QEMU evidence rebuilds
`build/os/simpleos_riscv64_desktop_service.elf` and passes serial, SSH banner,
HTTP `200`, QMP screendump/nonblank GPU readback, and WM marker rows. The
aggregate now advances to
`blocked:fpga-serial:blocked:missing-fpga-uart-terminal`; FPGA UART evidence,
Engine2D Vulkan evidence, RenderDoc evidence, host-WM evidence, and structured
comparison are still incomplete.
With `-ProbeHostVulkan`, the combined wrapper also asks the Engine2D/RenderDoc
normalizer to record host Vulkan diagnostics. The aggregate checker echoes
`simpleos_windows_vulkaninfo_status`, Vulkan instance/device rows,
`simpleos_windows_vulkan_sdk_tools_status`,
`simpleos_windows_renderdoc_tool_status`,
`simpleos_windows_vulkan_host_readiness_status`, and the required
`gui_web_2d_vulkan_browser_backing_*` rows. Current Windows evidence proves
host Vulkan discovery only: `vulkaninfo` passes with instance `1.3.301` on
`Intel(R) UHD Graphics 770`, while SDK tools and RenderDoc are missing and
browser backing is `fail` with
`focused-browser-backing-required`.

## Scenario: Static Matrix Status

1. Validate all QEMU RV64 required profile capabilities.
2. Validate the FPGA RV64 allowed capability set.
3. Confirm the static profile goal reports
   `profiles-ready-live-evidence-required`.

That final status is intentional: static configuration passing is not live
QEMU, Vulkan, RenderDoc, or WM comparison evidence.
