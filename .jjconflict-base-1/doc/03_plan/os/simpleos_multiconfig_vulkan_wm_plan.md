# SimpleOS Multi-Config Vulkan WM Plan

## Status
Active SPipe lane: `.spipe/simpleos-multiconfig-vulkan-wm/state.md`.

This plan coordinates five separable implementation tracks:

1. QEMU RV64 desktop profile with serial, SSH, HTTP/webserver, GPU/framebuffer, WM, Simple2D/Engine2D, Vulkan, and RenderDoc evidence.
2. FPGA RV64 serial profile with UART terminal only until hardware evidence proves more.
3. Simple2D over Engine2D on the QEMU GPU/framebuffer path.
4. Vulkan-over-Engine2D capture through SimpleOS RenderDoc instrumentation.
5. SimpleOS WM comparison against host WM RenderDoc/readback logs.

## Config Matrix

| Profile | Arch | Boot target | Terminal | SSH | HTTP | GPU | WM | Vulkan | RenderDoc | Host compare |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `qemu-riscv64-desktop` | riscv64 | QEMU `virt` | serial + graphical | host `2222` | host `8080` | virtio/ramfb evidence | required | required | required | required |
| `fpga-riscv64-serial` | riscv64 | FPGA softcore/min profile | UART serial | blocked | blocked | blocked | blocked | blocked | blocked | blocked |

FPGA remains fail-closed for non-serial capabilities. A future board-specific lane may add network, framebuffer, or accelerator support only after hardware inventory, boot logs, and regression checks prove the new capability.

## Implementation Tracks

### Track A: Config Contract
Owner files:
- `src/os/simpleos_config_matrix.spl`
- `test/01_unit/os/simpleos_config_matrix_spec.spl`
- `scripts/check/check_simpleos_multiconfig_live_evidence.spl`
- `scripts/check/check-simpleos-multiconfig-live-evidence.ps1`

Required behavior:
- Publish profile constructors for QEMU RV64 desktop and FPGA RV64 serial.
- Return `ready` only for capabilities supported by the selected profile.
- Return `blocked:<reason>` for FPGA non-serial requests.
- Expose a single text summary for scripts and docs to inspect.
- Expose the aggregate `simpleos_multiconfig_live_required_evidence_keys()`
  status set so live wrappers have one final fail-closed completion gate after
  per-lane QEMU, FPGA, Engine2D, RenderDoc, and WM comparison evidence passes.
- Provide `scripts/check/check_simpleos_multiconfig_live_evidence.spl` as the
  canonical aggregate status emitter. With no live artifacts it must print the
  QEMU/FPGA/Engine2D/RenderDoc/WM status rows and exit blocked/nonzero.
- Accept a wrapper-produced evidence file through `--evidence <path>` or
  `SIMPLEOS_MULTICONFIG_EVIDENCE`. The file is line-oriented `key=value` text
  containing the six keys from `simpleos_multiconfig_live_required_evidence_keys()`.
  Wrappers may alternatively write the raw per-lane keys named by
  `simpleos_qemu_service_required_evidence_keys()`,
  `simpleos_fpga_serial_required_evidence_keys()`,
  `simpleos_engine2d_vulkan_required_evidence_keys()`,
  `simpleos_renderdoc_artifact_required_evidence_keys()`,
  `simpleos_wm_structured_compare_required_evidence_keys()`, and
  `simpleos_wm_renderdoc_required_evidence_keys()`; the checker derives the
  six aggregate lane statuses from those raw rows.
  RenderDoc raw-row ingestion is intentionally strict: raw
  `simpleos_renderdoc_rdc_magic=RDOC` is not sufficient unless
  `simpleos_renderdoc_rdc_magic_status=pass` is present too.
  On Windows, keep that fail-closed contract covered with
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-rdoc-raw-row-gate.ps1`.
  This is synthetic aggregate-contract smoke only; it does not replace real
  SimpleOS `.rdc`, QEMU WM, host WM, or RenderDoc log evidence.
- On Windows, use
  `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-multiconfig-live-evidence.ps1`
  as the combined operator entrypoint. It runs the QEMU, FPGA, WM compare, and
  Engine2D/RenderDoc wrappers in order, preserves intermediate evidence files
  under `build/simpleos_multiconfig_live_evidence/`, writes the final merged
  evidence file to
  `build/simpleos_multiconfig_live_evidence/simpleos-multiconfig-live.env`,
  then runs the aggregate checker against that file.

### Track B: QEMU RV64 Services
Owner candidates:
- `src/os/qemu_systest_contract.spl`
- `src/os/kernel/arch/riscv64/rv64_hosted_*.spl`
- `scripts/check/` QEMU wrappers
- `scripts/check/check-simpleos-qemu-rv64-desktop-evidence.ps1`
- `src/os/simpleos_config_matrix.spl`

Required behavior:
- Use explicit host port forwarding for SSH `2222` and webserver `8080`.
- Preserve the pure descriptor exposed by `qemu_riscv64_desktop_qemu_args()`:
  `-netdev user,id=rvnet,hostfwd=tcp::2222-:22,hostfwd=tcp::8080-:8080`,
  `virtio-net-pci,netdev=rvnet`,
  `virtio-gpu-pci,disable-modern=on,disable-legacy=off`, headless display,
  QMP `tcp:127.0.0.1:4444,server,nowait`, and serial file logging.
- Reuse the same descriptor through `src/os/qemu_systest_contract.spl`
  desktop accessors (`riscv64_desktop_qemu_args()` and
  `riscv64_desktop_qemu_args_status()`) when a live system wrapper is added.
- Emit the live rows named by `simpleos_qemu_service_required_evidence_keys()`:
  serial console status, SSH banner, SSH probe status, HTTP status code, HTTP
  probe status, GPU readback status, and WM marker status.
- On Windows, run
  `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1`
  to emit raw QEMU service rows into
  `build/simpleos_multiconfig_live_evidence/qemu-rv64-desktop.env`.
  The wrapper detects `qemu-system-riscv64`, required kernel/disk artifacts,
  host ports `2222`/`8080`, and writes fail-closed rows for missing serial,
  SSH, HTTP, GPU, and WM evidence.
- Use `-RunLiveBoot` on the same wrapper after canonical artifacts exist to
  launch QEMU, capture serial output under
  `build/os/systest/qemu-riscv64-desktop/serial.log`, wait for FS-exec or
  network/http serial markers, expose QMP on `127.0.0.1:4444`, capture a QMP
  `screendump` PPM after `Display service ready`, validate it as nonblank, and
  probe SSH `2222` plus HTTP `8080`. Live mode emits
  `simpleos_qemu_rv64_live_boot_status`,
  `simpleos_qemu_rv64_qemu_exit_status`,
  `simpleos_qemu_rv64_qmp_status`,
  `simpleos_qemu_rv64_screendump_status`, and
  `simpleos_qemu_rv64_screendump_nonblank_status`. It also captures QEMU
  stdout/stderr under the artifact directory and emits
  `simpleos_qemu_rv64_stdout_path`, `simpleos_qemu_rv64_stderr_path`, and
  `simpleos_qemu_rv64_process_output_status`, so early QEMU exits keep their
  diagnostic output. It still blocks structured WM completion until WM compare
  and RenderDoc evidence are available.
- Emit artifact-diagnostic rows for canonical desktop, legacy smoke, FPGA, and
  storage-probe candidates:
  `simpleos_qemu_rv64_canonical_kernel_status`,
  `simpleos_qemu_rv64_legacy_kernel_status`,
  `simpleos_qemu_rv64_fpga_kernel_status`,
  `simpleos_qemu_rv64_canonical_image_status`,
  `simpleos_qemu_rv64_storage_probe_image_status`,
  `simpleos_qemu_rv64_kernel_candidate_status`, and
  `simpleos_qemu_rv64_image_candidate_status`. These rows guide operators but
  do not satisfy the QEMU desktop gate unless the canonical SMF-FS kernel,
  FAT32 image, and live probes pass.
- Use `-AttemptBuild` on the QEMU wrapper, or on the combined Windows wrapper,
  when the operator wants fresh build evidence before QEMU preflight. The
  wrapper runs `src\compiler_rust\target\debug\simple.exe os build --arch=riscv64`,
  writes `build/os/systest/qemu-riscv64-desktop/rv64-build.log`, refreshes the
  artifact candidate rows, and emits
  `simpleos_qemu_rv64_build_attempted`,
  `simpleos_qemu_rv64_build_status`,
  `simpleos_qemu_rv64_build_exit_code`,
  `simpleos_qemu_rv64_native_build_exit_code`, and
  `simpleos_qemu_rv64_build_log_path`. The wrapper also records the selected
  nested Simple binary, build backend, compiler, and disk-image build rows. On
  this Windows host the passing build path is:
  `-BuildBackend cranelift -BuildCc C:\dev\install\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin\clang.exe`.
  That path uses `src\compiler_rust\target\debug\simple.exe` as the nested
  Simple binary, emits `simpleos_qemu_rv64_build_status=pass`, produces
  `build/os/simpleos_riscv64_smf_fs.elf`, and, with `-BuildDiskImage`,
  produces `build/os/fat32-riscv64.img` through `scripts/os/make_os_disk.c`.
  The default LLVM backend remains blocked on this host because the native
  backend is unavailable.
- Use `-BuildDesktopServiceKernel` when the operator needs current-source QEMU
  desktop service evidence. On 2026-06-26 this path rebuilt
  `build/os/simpleos_riscv64_desktop_service.elf`, booted QEMU, and passed
  serial, SSH banner, HTTP `200`, QMP screendump/nonblank GPU readback, and WM
  marker rows with `simpleos_qemu_rv64_blocker=pass`.
- Keep serial probes as the first boot oracle.
- Add bounded SSH and HTTP probes after preflight alive markers.
- Write artifacts under `build/os/systest/qemu-riscv64-desktop/`.

### Track C: FPGA RV64 Serial
Owner candidates:
- `src/os/kernel/arch/riscv64/platform/`
- `scripts/check/check-riscv64-fpga-simpleos-preflight.shs`
- `doc/08_tracking/hardware/`

Required behavior:
- Keep UART as the only terminal and operator control path.
- Report missing board/toolchain as `blocked:<reason>`.
- Reject SSH, HTTP, GPU, framebuffer, WM, Vulkan, and RenderDoc requests for this profile.
- Build the current-source serial-only entry
  `examples/09_embedded/simple_os/arch/riscv64/fpga_serial_entry.spl` to
  `build/os/simpleos_riscv64_fpga.elf` when `-BuildFpgaSerialKernel` is used.
- On Windows, use
  `scripts/check/check-simpleos-fpga-rv64-serial-evidence.ps1` to write
  `build/simpleos_multiconfig_live_evidence/fpga-rv64-serial.env` from serial
  device/log, toolchain, and bitstream evidence before handing the file to the
  aggregate checker.
- Add `-ProbeSerialPorts` when the operator wants a Windows COM-port inventory
  beside the FPGA evidence. The wrapper writes diagnostic rows such as
  `simpleos_fpga_serial_port_probe_status`,
  `simpleos_fpga_serial_port_probe_count`,
  `simpleos_fpga_serial_port_probe_ports`, and
  `simpleos_fpga_serial_device_candidate_status`, plus a sidecar
  `fpga-rv64-serial-ports.env`. Port presence is not boot evidence: UART
  terminal completion still requires the configured serial log to contain the
  FPGA boot marker.
- Add `-CaptureSerial -SerialDevice <COMx>` when the operator wants the wrapper
  to collect the UART log directly. Capture is bounded by
  `-CaptureTimeoutSeconds` and defaults to 115200 baud. The wrapper writes
  `simpleos_fpga_serial_capture_*` rows and keeps the gate blocked unless the
  captured or supplied log contains `SIMPLEOS_FPGA_RISCV64_SERIAL_BOOT` and the
  toolchain/bitstream rows pass.
- The combined Windows wrapper forwards live UART capture with
  `-CaptureFpgaSerial -FpgaSerialDevice <COMx>` plus
  `-FpgaSerialCaptureTimeoutSeconds` and `-FpgaSerialCaptureBaudRate`.
- Emit the rows named by `simpleos_fpga_serial_required_evidence_keys()`:
  board profile, expected entry/kernel, UART terminal status, serial device,
  serial boot marker, toolchain status, bitstream status, and blocked
  SSH/HTTP/GPU/WM/Vulkan/RenderDoc statuses.

### Track D: Simple2D / Engine2D / Vulkan
Owner candidates:
- `src/lib/common/ui/draw_ir.spl`
- `src/lib/common/ui/window_scene_draw_ir.spl`
- `src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl`
- `doc/04_architecture/ui/simple_gui_stack.md`

Required behavior:
- Route Simple2D drawing through Engine2D backend lanes.
- Add QEMU GPU/framebuffer readback evidence before claiming acceleration.
- Treat CPU fallback as explicit fallback evidence, not Vulkan proof.
- Require backend name, device/readback checksum, viewport metadata, and nonblank proof.
- Use `qemu_riscv64_engine2d_vulkan_bridge_plan()` as the implementation
  target for QEMU SimpleOS: `virtio_gpu` owns the QEMU framebuffer drawing
  surface, `vulkan` owns the Engine2D processing backend, Simple2D commands
  enter through `draw_ir-to-engine2d`, and both Engine2D device readback and
  QMP screendump readback are required.
- On Windows, use
  `scripts/check/check-simpleos-engine2d-renderdoc-evidence.ps1` with
  `-BaseEvidencePath build/simpleos_multiconfig_live_evidence/wm-host-compare.env`
  to normalize Engine2D/Vulkan and RenderDoc artifacts into the aggregate
  evidence file. It can read `build/gui-web-2d-vulkan-env/evidence.env`, QEMU
  screendump readback, SimpleOS `.rdc`, capture logs, and QEMU/host WM
  RenderDoc logs. If the Engine2D source evidence lacks ARGB viewport metadata
  but the QEMU screendump PPM is present, the wrapper derives diagnostic
  viewport rows from the PPM header and emits
  `simpleos_qemu_gpu_readback_width`,
  `simpleos_qemu_gpu_readback_height`, and
  `simpleos_qemu_gpu_readback_dimensions_status`. These rows improve audit
  detail but do not satisfy the Vulkan backend requirement by themselves.
  The wrapper also reports source-usability rows so stale GUI/browser setup
  output cannot be mistaken for SimpleOS Engine2D Vulkan proof:
  `simpleos_engine2d_source_evidence_mode`,
  `simpleos_engine2d_source_simple_status`,
  `simpleos_engine2d_source_browser_backing_status`,
  `simpleos_engine2d_source_evidence_usable_status`,
  `simpleos_engine2d_source_evidence_usable_reason`, and
  `simpleos_engine2d_runtime_backend_reason`. A current stale
  `--browser-backing` source with `gui_web_2d_vulkan_simple_status=not-run`
  is reported as
  `simpleos_engine2d_source_evidence_usable_status=blocked` with reason
  `source-browser-backing-only-simple-not-run`.
- Add `-ProbeHostVulkan` to the same wrapper, or to the combined Windows
  wrapper, when the operator wants host Vulkan readiness diagnostics beside the
  SimpleOS gates. This probe records `vulkaninfo --summary`, Chrome/Electron
  presence, Vulkan SDK tool visibility, RenderDoc tool visibility, and the
  required browser-backing rows. These rows are diagnostics only: Windows host
  Vulkan discovery and installed browsers do not prove SimpleOS Engine2D
  Vulkan, Chrome Vulkan backing, Electron Vulkan backing, or RenderDoc capture.
- Emit the rows named by `simpleos_engine2d_vulkan_required_evidence_keys()`:
  runtime backend, Engine2D scene, Simple2D command status, Vulkan device name,
  viewport width/height, readback checksum, nonblank readback status, and QEMU
  GPU readback status.
- Keep `simpleos_engine2d_vulkan_bridge_required_keys()` aligned with the live
  wrapper rows so a CPU fallback, missing
  `virtio-gpu-pci,disable-modern=on,disable-legacy=off`, missing QMP
  screendump, or `capture-html` mode cannot satisfy the SimpleOS bridge.
- `scripts/check/check-simpleos-engine2d-renderdoc-evidence.ps1` emits those
  bridge rows, and `scripts/check/check_simpleos_multiconfig_live_evidence.spl`
  prints `simpleos_engine2d_vulkan_bridge_status` as a diagnostic beside the
  six aggregate completion gates. The diagnostic does not replace live
  Engine2D Vulkan/readback proof; it prevents the live rows from drifting away
  from the intended QEMU SimpleOS bridge.
- The same normalizer now emits a source-audit block for the current QEMU
  implementation: `simpleos_engine2d_source_qemu_entry_status`,
  `simpleos_engine2d_source_baremetal_core_status`,
  `simpleos_engine2d_source_virtio_surface_status`,
  `simpleos_engine2d_source_vulkan_session_status`,
  `simpleos_engine2d_source_current_draw_path`,
  `simpleos_engine2d_source_target_processing_backend`, and
  `simpleos_engine2d_source_bridge_audit_status`. A pass on the first four rows
  means the expected source surfaces exist. It is still not Vulkan proof. The
  current source audit reports
  `simpleos_engine2d_source_current_draw_path=freestanding-display-runtime` and
  `simpleos_engine2d_source_bridge_audit_status=blocked:desktop-service-not-wired-to-vulkan-engine2d-session`;
  the next implementation step is to wire the QEMU desktop-service draw path to
  the Vulkan Engine2D session and then prove it with device readback.

### Track E: RenderDoc and WM Comparison
Owner candidates:
- `scripts/tool/renderdoc-evidence.shs`
- `scripts/setup/setup-gui-web-2d-vulkan-env.shs`
- `scripts/check/check-gui-renderdoc-feature-coverage-status.shs`
- `src/os/compositor/`
- `src/os/desktop/`
- `src/os/simpleos_config_matrix.spl`

Required behavior:
- Capture SimpleOS Engine2D/Vulkan with `capture-simple` or the current Simple in-application RenderDoc path.
- Capture host WM baseline separately and record backend/device identity.
- Validate `.rdc` files by `RDOC` magic.
- Keep WM scene identity separate from RenderDoc/Engine2D scene identity. The
  Windows WM wrapper defaults `-WmSceneName` to
  `simpleos-desktop-four-windows` and `-RenderdocSceneName` to
  `vulkan-engine2d`.
- Emit the rows named by `simpleos_renderdoc_artifact_required_evidence_keys()`:
  capture mode, `.rdc` path, `.rdc` magic, `.rdc` size, capture log path,
  capture log status, Simple runtime backend, Simple scene, RenderDoc helper
  status, QEMU WM log path, and host WM log path.
- Compare structured WM state first: windows, titlebar controls, taskbar/dock, command surfaces, focus, motion mode, and rendered readback metadata.
- On Windows, use
  `scripts/check/check-simpleos-wm-host-compare-evidence.ps1` with
  `-BaseEvidencePath build/simpleos_multiconfig_live_evidence/qemu-rv64-desktop.env`
  to merge QEMU service rows with host/QEMU WM comparison rows. The wrapper
  validates QEMU and host PPM captures, exact byte mismatch count, RenderDoc
  `.rdc` magic/size, capture log status, and QEMU/host WM RenderDoc log paths.
  Add `-AttemptHostWmCapture` to ask the existing hosted-WM capture entrypoint
  to write `host-wm.ppm` before validation. The attempt emits
  `simpleos_host_wm_capture_attempted`, mode, status, exit code, and log path
  rows. Use `-HostCaptureTimeoutSeconds` to bound the child capture process.
  A timeout, crashed, missing, or fallback capture is diagnostic only and does
  not satisfy the host-WM evidence gate. The current Windows wrapper avoids
  the hosted file-output path by asking the entrypoint to emit a
  marker-delimited compact rectangle scene on stdout, then materializes that
  artifact as a P6 `host-wm.ppm` and records
  `simpleos_host_wm_capture_mode=hosted-wm-capture-stdout-ppm`.
  The wrapper also classifies the parsed PPM artifacts with
  `simpleos_wm_qemu_capture_kind`, `simpleos_wm_host_capture_kind`, dimensions,
  and `simpleos_wm_argb_diff_reason`. These rows are diagnostics; the wrapper
  must not promote a virtio-gpu test pattern or a small hosted diagnostic crop
  into QEMU/host WM scene, titlebar, or taskbar evidence.
- Emit the rows named by `simpleos_wm_structured_compare_required_evidence_keys()`:
  QEMU/host scene names, window counts, focus IDs, titlebar status, taskbar
  status, RenderDoc log compare status, ARGB diff status, and ARGB mismatch
  count.
- Pixel/ARGB comparison is supplemental unless all backends and captures are proven.
- Keep `simpleos_wm_renderdoc_required_evidence_keys()` aligned with any
  wrapper that aggregates QEMU SimpleOS WM and host WM RenderDoc/readback logs.
- Run `scripts/check/check-simpleos-rdoc-raw-row-gate.ps1` after changes to
  raw RenderDoc ingestion. It verifies that raw `RDOC` without
  `simpleos_renderdoc_rdc_magic_status=pass` still blocks both RenderDoc
  artifact and WM RenderDoc aggregate evidence, and that the same synthetic
  rows pass only when the explicit magic-status row is present.

## Evidence Contract

Completion requires all of these evidence rows:

| Key | Pass value | Notes |
| --- | --- | --- |
| `simpleos_multiconfig_qemu_profile_status` | `pass` | QEMU profile supports required services and GPU/WM path. |
| `simpleos_multiconfig_fpga_profile_status` | `pass` | FPGA serial-only restrictions are enforced. |
| `simpleos_fpga_board_profile` | `fpga-riscv64-serial` | FPGA lane remains on the serial-only profile. |
| `simpleos_fpga_uart_terminal_status` | `pass` | UART terminal is the only interactive control path. |
| `simpleos_fpga_serial_boot_marker` | non-empty | Board serial log contains a SimpleOS boot marker. |
| `simpleos_fpga_ssh_status` | `blocked` | SSH must not silently become enabled on FPGA. |
| `simpleos_fpga_gpu_status` | `blocked` | GPU/desktop proof belongs to QEMU until board evidence expands FPGA. |
| `simpleos_qemu_serial_console_status` | `pass` | Serial boot oracle is alive before service probes run. |
| `simpleos_qemu_rv64_ssh_banner` | non-empty | Expected SSH server banner through host port `2222`. |
| `simpleos_qemu_rv64_ssh_probe_status` | `pass` | Bounded SSH probe through host port `2222`. |
| `simpleos_qemu_rv64_http_status_code` | `200` | Webserver returns HTTP 200 through host port `8080`. |
| `simpleos_qemu_rv64_http_probe_status` | `pass` | Bounded webserver probe through host port `8080`. |
| `simpleos_qemu_gpu_readback_status` | `pass` | Nonblank readback, backend identity, viewport metadata. |
| `simpleos_qemu_gpu_readback_dimensions_status` | `pass` | Diagnostic QEMU screendump dimensions are parseable. |
| `simpleos_qemu_wm_marker_status` | `pass` | Guest WM marker proves the desktop path reached the guest. |
| `simpleos_renderdoc_simple_runtime_backend` | `vulkan` | RenderDoc evidence proves the Simple runtime used Vulkan, not CPU fallback. |
| `simpleos_renderdoc_simple_scene` | `vulkan-engine2d` | RenderDoc evidence names the Engine2D/Vulkan scene. |
| `simpleos_engine2d_runtime_backend` | `vulkan` | Engine2D runtime path must be Vulkan, not CPU/software fallback. |
| `simpleos_engine2d_source_evidence_usable_status` | `pass` | Browser-backing-only or failed source evidence is diagnostic, not SimpleOS Vulkan proof. |
| `simpleos_engine2d_runtime_backend_reason` | `pass` | Explains why the SimpleOS Engine2D backend is not Vulkan. |
| `simpleos_engine2d_scene` | `vulkan-engine2d` | The Simple2D scene used for Vulkan proof. |
| `simpleos_simple2d_command_status` | `pass` | Simple2D commands reached the Engine2D path. |
| `simpleos_engine2d_readback_checksum` | non-empty | Device readback checksum for the rendered scene. |
| `simpleos_engine2d_readback_nonblank_status` | `pass` | Readback is nonblank and viewport-sized. |
| `simpleos_renderdoc_capture_mode` | `capture-simple` | Simple in-application RenderDoc path, not host/browser-only capture. |
| `simpleos_renderdoc_rdc_path` | non-empty | Path to the SimpleOS `.rdc` artifact. |
| `simpleos_renderdoc_rdc_magic_status` | `pass` | SimpleOS `.rdc` exists and starts with `RDOC`. |
| `simpleos_renderdoc_rdc_status` | `pass` | Direct status row for `.rdc` magic readiness. |
| `simpleos_renderdoc_rdc_size_bytes` | `> 4` | Header-only `.rdc` files are blocked. |
| `simpleos_renderdoc_capture_log_status` | `pass` | Capture helper log completed successfully. |
| `simpleos_renderdoc_artifact_blocker_reason` | `pass` | Explains the first missing RenderDoc artifact gate. |
| `simpleos_renderdoc_qemu_wm_log_path` | non-empty | QEMU WM RenderDoc/log evidence for the same scene. |
| `simpleos_renderdoc_host_wm_log_path` | non-empty | Host WM RenderDoc/log evidence for the same scene. |
| `simpleos_wm_renderdoc_log_compare_status` | `pass` | RenderDoc/log comparison for the same QEMU and host WM scene. |
| `simpleos_wm_renderdoc_log_compare_reason` | `pass` | Explains missing, malformed, or mismatched RenderDoc logs. |
| `simpleos_wm_renderdoc_log_compare_mode` | `structured-renderdoc-log-compare` | Comparison mode; nonempty log files alone are not enough. |
| `simpleos_wm_renderdoc_qemu_log_scene` | `simpleos-desktop-four-windows` | QEMU RenderDoc log scene parsed from structured log fields. |
| `simpleos_wm_renderdoc_host_log_scene` | `simpleos-desktop-four-windows` | Host RenderDoc log scene parsed from structured log fields. |
| `simpleos_wm_renderdoc_qemu_log_backend` | `vulkan` | QEMU RenderDoc log backend must prove Vulkan. |
| `simpleos_wm_renderdoc_host_log_backend` | `vulkan` | Host RenderDoc log backend must prove Vulkan. |
| `simpleos_wm_qemu_capture_kind` | `qemu-wm-rect-scene` or stronger WM-scene artifact | `qemu-virtio-gpu-test-pattern` is GPU readback proof only, not WM scene proof. |
| `simpleos_wm_host_capture_kind` | `hosted-wm-rect-scene` or stronger WM-scene artifact | `hosted-wm-diagnostic-crop` is host capture diagnostics only, not full-scene parity. |
| `simpleos_wm_argb_diff_reason` | `pass` | Explains blocked diffs, for example `qemu-gpu-test-pattern-not-wm-scene`. |
| `simpleos_wm_argb_diff_status` | `pass` | ARGB diff exists for the same scene after structured state matches. |
| `simpleos_wm_argb_mismatch_count` | `0` | Nonzero mismatches keep the comparison blocked. |
| `simpleos_wm_qemu_host_compare_status` | `pass` | QEMU WM and host WM structured comparison passes. |
| `simpleos_multiconfig_live_status` | `pass` | Aggregate gate over QEMU service, FPGA serial, Engine2D Vulkan, RenderDoc artifact, structured WM compare, and WM RenderDoc statuses. |

Host-unavailable is an allowed local result, but it is not completion.
The canonical aggregate checker is
`scripts/check/check_simpleos_multiconfig_live_evidence.spl`. It emits
`simpleos_multiconfig_live_status=blocked:qemu-service:blocked:missing-qemu-serial-console`
until real live evidence rows replace the default missing-evidence records.
The same operator output also prints
`simpleos_renderdoc_artifact_required_evidence_keys` and
`simpleos_wm_renderdoc_required_evidence_keys` so RDOC magic/status and WM
RenderDoc comparison requirements are visible without opening the source
contract.
Wrappers can hand off a `key=value` evidence file with these rows:

```text
simpleos_qemu_service_evidence_status=pass
simpleos_fpga_serial_evidence_status=pass
simpleos_engine2d_vulkan_evidence_status=pass
simpleos_renderdoc_artifact_evidence_status=pass
simpleos_wm_structured_compare_evidence_status=pass
simpleos_wm_renderdoc_evidence_status=pass
```

If a wrapper writes raw evidence instead, the aggregate checker derives the six
status rows from the detailed contract keys. For example, QEMU service rows
such as `simpleos_qemu_serial_console_status`,
`simpleos_qemu_rv64_ssh_banner`, `simpleos_qemu_rv64_http_status_code`,
`simpleos_qemu_gpu_readback_status`, and `simpleos_qemu_wm_marker_status`
derive `simpleos_qemu_service_evidence_status`. Missing or nonpassing raw rows
remain blocked.

The Windows combined wrapper
`scripts/check/check-simpleos-multiconfig-live-evidence.ps1` is the quickest
local way to produce that raw merged file. Its current host result is expected
to exit nonzero until all six gates pass. Current QEMU desktop-service evidence
passes with `-BuildDesktopServiceKernel -RunLiveBoot`, so
`simpleos_qemu_service_evidence_status=pass`. The aggregate now advances to
`simpleos_multiconfig_live_status=blocked:fpga-serial:blocked:missing-fpga-uart-terminal`;
Engine2D Vulkan, RenderDoc, host-WM, and structured comparison evidence are
also still incomplete. When that merged file contains Windows wrapper rows, the aggregate
checker echoes `simpleos_multiconfig_windows_wrapper` and the QEMU, FPGA, WM,
Engine2D, and aggregate exit-code diagnostics beside the six live gate rows.
When run with `-AttemptBuild -BuildDiskImage`, the same aggregate output also
echoes the QEMU RV64 build attempt rows, selected nested Simple binary, build
backend/compiler, canonical artifact statuses, disk-image builder rows, live
boot status, QEMU exit status, and the current QEMU blocker.
When run with `-AttemptHostWmCapture`, the same aggregate output echoes the
hosted-WM capture attempt rows. On the current Windows debug driver the wrapper
records `simpleos_host_wm_capture_status=pass` and
`simpleos_wm_host_ppm_status=pass` through the stdout compact-scene path.
Use `-HostCaptureTimeoutSeconds <n>` on the combined wrapper to forward the
same timeout bound to the focused WM host-capture wrapper.
The aggregate also echoes the PPM dimensions, capture kinds, ARGB diff status,
ARGB reason, and mismatch count. The refreshed live WM comparison over
`build/simpleos_multiconfig_live_evidence/qemu-rv64-desktop-live-refresh.env`
writes
`build/simpleos_multiconfig_live_evidence/wm-host-compare-live-refresh.env`:
both QEMU and host captures are `320x240` rectangle-scene PPM artifacts, titlebar
and taskbar checks pass on both sides, and the exact ARGB mismatch count is
zero. The current QEMU screendump is classified as
`simpleos_wm_qemu_capture_kind=qemu-wm-rect-scene`, while the host artifact is
`simpleos_wm_host_capture_kind=hosted-wm-rect-scene`; the ARGB status and
reason are `pass`, and `simpleos_wm_argb_mismatch_count=0`. Therefore
`simpleos_wm_structured_compare_evidence_status` remains
`blocked:missing-renderdoc-log-compare` until the QEMU/host RenderDoc log
comparison rows pass. Stale captures may still report
`qemu-gpu-test-pattern-not-wm-scene`; in that case rerun the QEMU desktop
service wrapper with `-BuildDesktopServiceKernel -RunLiveBoot` before trusting
the WM compare output.
When run with `-ProbeHostVulkan`, the same aggregate output echoes Windows host
readiness rows such as `simpleos_windows_vulkaninfo_status`,
`simpleos_windows_vulkan_sdk_tools_status`,
`simpleos_windows_renderdoc_tool_status`,
`simpleos_windows_vulkan_host_readiness_status`, and
`gui_web_2d_vulkan_browser_backing_status`. On the current Windows host,
`vulkaninfo` reports Vulkan instance `1.3.301` and device
`Intel(R) UHD Graphics 770`, while SDK tools and RenderDoc are missing and
browser backing remains
`fail`/`focused-browser-backing-required`. The aggregate live status therefore
remains blocked.
For Engine2D/RenderDoc normalization, the aggregate also echoes the
source-usability and artifact blocker rows. A current Windows run reports
`simpleos_engine2d_source_evidence_mode=--browser-backing`,
`simpleos_engine2d_source_simple_status=not-run`,
`simpleos_engine2d_source_evidence_usable_status=blocked`,
`simpleos_engine2d_source_evidence_usable_reason=source-browser-backing-only-simple-not-run`,
`simpleos_engine2d_runtime_backend_reason=simple-vulkan-probe-not-run`,
`simpleos_renderdoc_artifact_blocker_reason=missing-simple-rdoc-magic`, and
`simpleos_wm_renderdoc_log_compare_reason=missing-qemu-and-host-renderdoc-logs`.
Those rows are intentionally fail-closed diagnostics; they do not relax the
required Vulkan backend, RDOC magic, or RenderDoc log comparison gates.
Windows can now run a native direct Simple Vulkan readback probe with
`scripts/check/check-vulkan-engine2d-readback.ps1`; the Engine2D/RenderDoc
normalizer exposes it through `-RunSimpleVulkanProbe`, and the combined Windows
wrapper forwards the same option. The direct probe writes
`vulkan_engine2d_readback_*` rows, and the aggregate echoes
`simpleos_engine2d_direct_readback_status`,
`simpleos_engine2d_direct_readback_reason`, and
`simpleos_engine2d_direct_readback_exit_code`. It also echoes the Engine2D
bridge/backend rows, Vulkan device name, viewport, readback checksum, nonblank
status, and QEMU GPU readback path/dimensions so operators can distinguish
guest framebuffer proof from missing SimpleOS Vulkan backend proof. A current
noninvasive Windows run over
`build/simpleos_multiconfig_live_evidence/wm-host-compare-live-refresh.env`
writes
`build/simpleos_multiconfig_live_evidence/engine2d-renderdoc-live-preflight.env`:
QEMU GPU readback remains `pass` at `320x240`, Windows `vulkaninfo` reports
`Intel(R) UHD Graphics 770`, but the direct Simple Vulkan probe is
`preflight-only`, `simpleos_engine2d_processing_backend=missing`, and
`simpleos_engine2d_readback_nonblank_status=blocked:source-evidence-not-usable`.
The aggregate therefore keeps
`simpleos_engine2d_vulkan_evidence_status=blocked:missing-engine2d-vulkan-backend`.
The refreshed source-audit artifact
`build/simpleos_multiconfig_live_evidence/engine2d-renderdoc-live-source-audit.env`
also records that the QEMU desktop entry, baremetal Engine2D core, Engine2D
VirtIO surface contract, and Engine2D Vulkan session source are present, while
`simpleos_engine2d_source_bridge_audit_status` remains
`blocked:desktop-service-not-wired-to-vulkan-engine2d-session`.
It also echoes the existing Simple process count and limit when the Windows
process-count guard blocks a new probe launch. A current Windows smoke run
finds more than 25,000 existing `simple.exe` processes and stops before
launching another child, so the normalized blocker remains fail-closed.
For noninvasive host-state recording, run the same path with
`-SimpleVulkanProbePreflightOnly -AllowHighSimpleProcessCount`; that records
the process count and emits `simpleos_engine2d_direct_readback_reason=preflight-only`
without launching a Simple Vulkan evidence child.
The standalone Windows inventory helper
`scripts/check/check-simple-process-inventory.ps1` writes
`simple_process_inventory_*` rows and defaults to dry-run mode. The combined
Windows wrapper can merge those rows with `-RunSimpleProcessInventory`. Process
termination requires an explicit `-Kill -ConfirmText KILL_SIMPLE_PROCESSES`
invocation of the inventory helper; the combined wrapper does not kill
processes.

## Verification Plan

Initial non-hardware verification:
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/01_unit/os/simpleos_config_matrix_spec.spl --mode=interpreter`
- On Windows: `SIMPLE_LIB=src .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean`
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple scripts/check/check_simpleos_multiconfig_live_evidence.spl --mode=interpreter`
  should print the aggregate rows and currently exit nonzero until live
  QEMU/FPGA/Vulkan/RenderDoc/WM evidence is supplied.
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence build/simpleos_multiconfig_live_evidence/passing.env --mode=interpreter`
  should exit `0` only when the evidence file contains all six passing status
  rows.
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/simpleos_config_matrix.spl test/01_unit/os/simpleos_config_matrix_spec.spl`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

Live verification, when host support is available:
- QEMU RV64 boot with serial, SSH, HTTP, GPU readback, and WM markers.
- Windows combined evidence pass:
  `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-multiconfig-live-evidence.ps1`
  should produce
  `build/simpleos_multiconfig_live_evidence/simpleos-multiconfig-live.env` and
  return the aggregate checker exit code.
- Windows combined build preflight:
  `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-multiconfig-live-evidence.ps1 -AttemptBuild -BuildDiskImage -BuildBackend cranelift -BuildCc C:\dev\install\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin\clang.exe`
  should record QEMU RV64 build and FAT32 image status rows before the aggregate
  check. On the current host it records `simpleos_qemu_rv64_build_status=pass`,
  `simpleos_qemu_rv64_disk_image_build_status=pass`,
  `simpleos_qemu_rv64_canonical_kernel_status=pass`, and
  `simpleos_qemu_rv64_canonical_image_status=pass`, then remains blocked until
  live service/GPU/WM/FPGA/Vulkan/RenderDoc evidence passes.
- Windows combined build plus live serial smoke:
  `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-multiconfig-live-evidence.ps1 -AttemptBuild -BuildDiskImage -RunLiveBoot -BootTimeoutSeconds 20 -BuildBackend cranelift -BuildCc C:\dev\install\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin\clang.exe`
  currently boots the canonical image, records serial console pass markers, and
  reports `simpleos_qemu_rv64_qemu_exit_status=exited:0`; it remains blocked at
  missing SSH/banner service evidence because the guest exits before service
  probes can pass.
- Windows QEMU desktop-service live refresh:
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1 -RunLiveBoot -BootTimeoutSeconds 45 -KernelPath build/os/simpleos_riscv64_desktop_service.elf`
  should emit `simpleos_qemu_rv64_blocker=pass`,
  `simpleos_qemu_serial_console_status=pass`,
  `simpleos_qemu_rv64_ssh_probe_status=pass`,
  `simpleos_qemu_rv64_http_probe_status=pass`,
  `simpleos_qemu_gpu_readback_status=pass`, and
  `simpleos_qemu_wm_marker_status=pass` when the current desktop-service
  kernel and FAT32 image are present. If QEMU exits before boot, inspect
  `simpleos_qemu_rv64_stderr_path`.
- Windows combined host Vulkan probe:
  `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-multiconfig-live-evidence.ps1 -ProbeHostVulkan`
  should record Windows host readiness rows in the merged evidence file. On the
  current host it records `simpleos_windows_vulkaninfo_status=pass`,
  `simpleos_windows_vulkan_sdk_tools_status=blocked:sdk-tools-missing`,
  `simpleos_windows_renderdoc_tool_status=missing`, and
  `gui_web_2d_vulkan_browser_backing_status=fail`; this remains diagnostic
  until SimpleOS Engine2D readback, browser backing, and RenderDoc evidence pass.
- Windows combined current-source desktop/FPGA/WM/Vulkan refresh:
  `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-multiconfig-live-evidence.ps1 -BuildDesktopServiceKernel -BuildFpgaSerialKernel -AttemptHostWmCapture -HostCaptureTimeoutSeconds 20 -ProbeHostVulkan -BuildBackend cranelift -BuildCc C:\dev\install\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin\clang.exe -RunLiveBoot -BootTimeoutSeconds 45`
  should rebuild current QEMU desktop-service and FPGA serial kernels, run live
  QEMU service probes, refresh hosted-WM capture evidence with a bounded child
  process, record host Vulkan diagnostics, and then return the aggregate checker
  exit code. On the current host it is expected to remain nonzero while FPGA
  UART, SimpleOS Engine2D Vulkan, RDOC, and QEMU/host RenderDoc log evidence are
  missing.
- Windows direct Simple Vulkan probe smoke:
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-engine2d-renderdoc-evidence.ps1 -RunSimpleVulkanProbe -SimpleBinary bin\simple.exe -SimpleVulkanProbeTimeoutSeconds 5 -ProbeHostVulkan`
  should write direct readback rows and remain blocked if the Simple Vulkan
  evidence program times out or fails. On the current host the process-count
  guard records
  `simpleos_engine2d_direct_readback_reason=existing-simple-process-count-high`
  and keeps Engine2D Vulkan evidence blocked before launching another Simple
  child. Use `-AllowHighSimpleProcessCount` only after clearing or deliberately
  accepting that host process state.
- Windows direct Simple Vulkan preflight-only smoke:
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-engine2d-renderdoc-evidence.ps1 -RunSimpleVulkanProbe -SimpleVulkanProbePreflightOnly -AllowHighSimpleProcessCount -SimpleBinary bin\simple.exe -ProbeHostVulkan`
  should record process-count rows without launching a Simple Vulkan child and
  keep Engine2D Vulkan evidence blocked as `preflight-only`.
- Windows Simple process inventory dry run:
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simple-process-inventory.ps1`
  should emit `simple_process_inventory_*` rows and exit nonzero when the count
  exceeds the configured limit. It is diagnostic only unless the operator
  invokes the helper separately with `-Kill -ConfirmText KILL_SIMPLE_PROCESSES`.
- Windows FPGA serial-port inventory smoke:
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-fpga-rv64-serial-evidence.ps1 -ProbeSerialPorts`
  should emit `simpleos_fpga_serial_port_probe_*` rows and remain nonzero until
  real UART boot-marker, toolchain, and bitstream evidence are present. The
  combined wrapper forwards this with `-ProbeFpgaSerialPorts`.
- Windows FPGA UART capture smoke without hardware:
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-fpga-rv64-serial-evidence.ps1 -CaptureSerial -CaptureTimeoutSeconds 1`
  should emit `simpleos_fpga_serial_capture_status=blocked:missing-serial-device`
  and remain nonzero. On real hardware, provide `-SerialDevice <COMx>` plus
  toolchain and bitstream evidence; the combined wrapper forwards this with
  `-CaptureFpgaSerial -FpgaSerialDevice <COMx>`.
- Windows QEMU RV64 preflight:
  `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1`
  followed by
  `SIMPLE_LIB=src src/compiler_rust/target/debug/simple scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence build/simpleos_multiconfig_live_evidence/qemu-rv64-desktop.env --mode=interpreter`.
- `scripts/setup/setup-gui-web-2d-vulkan-env.shs --check`
- `scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc-simple`
- `scripts/tool/renderdoc-evidence.shs capture-simple`
- WM comparison wrapper emitting the evidence keys above.

## Done Rules

Do not mark the lane complete until:
- QEMU and FPGA profile checks pass.
- QEMU RV64 live service and GPU evidence pass.
- SimpleOS Vulkan/Engine2D and RenderDoc `.rdc` magic pass.
- Host WM and QEMU WM comparison passes with structured metadata.
- Docs and SPipe state list the commands and artifact paths actually used.
- `doc/06_spec` contains zero executable `*_spec.spl` files.
