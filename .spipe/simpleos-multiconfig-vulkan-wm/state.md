# Feature: simpleos-multiconfig-vulkan-wm

## Raw Request
use spipe dev skill. harden simle os for multiple config, for qemu riscv 64, fpga simpke riscv64. fpga config currently support serial port as terminal. qemu ssh webserver port support and gpu support. add impl vulkan over simple 2d engine. simple2d enigne on qemu gpu. vulkan renderdoc on simple os. and check simple os windows manager and check on qemu simple os and compare with host wm renderdoc log compare. make detail plans. add feature on simple os and wm.

## Task Type
feature

## Refined Goal
Harden SimpleOS with explicit QEMU RV64 and FPGA RV64 runtime profiles, then implement and verify a fail-closed Simple2D/Engine2D Vulkan and RenderDoc-backed WM comparison path for QEMU SimpleOS against host WM evidence.

## Acceptance Criteria
- AC-1: A canonical multi-config contract distinguishes `qemu-riscv64-desktop` from `fpga-riscv64-serial`, including terminal, SSH, HTTP/webserver, GPU, framebuffer, WM, Vulkan, RenderDoc, and host-comparison capabilities.
- AC-2: FPGA RV64 remains serial-terminal-only until hardware evidence expands it; requesting SSH, HTTP, GPU, WM, Vulkan, or RenderDoc on the FPGA profile returns a fail-closed reason, not a fallback PASS.
- AC-3: QEMU RV64 exposes expected SSH and webserver host-forwarding ports, a GPU/framebuffer path, Simple2D over Engine2D, Vulkan-over-Engine2D intent, and WM/RenderDoc comparison requirements.
- AC-4: The detailed implementation plan names architecture, design, implementation owners, specs, scripts, evidence artifacts, and host-unavailable behavior for QEMU RV64, FPGA RV64, Simple2D/Engine2D Vulkan, RenderDoc, and WM comparison.
- AC-5: Focused unit or system checks prove the config matrix and fail-closed capability validation without launching QEMU or requiring FPGA hardware.
- AC-6: Completion evidence for Vulkan/RenderDoc requires SimpleOS `.rdc` files with `RDOC` magic, Simple2D/Engine2D readback, QEMU WM evidence, host WM evidence, and a structured comparison report; screenshot-only or static bitmap parity is incomplete.
- AC-7: SPipe process/docs are updated where this lane changes canonical QEMU/GPU/RenderDoc/WM evidence commands, and final verification confirms `doc/06_spec` contains no executable `*_spec.spl` files.

## Scope Exclusions
- This first slice does not claim live QEMU boot, FPGA hardware boot, valid RenderDoc captures, or browser Vulkan backing are complete.
- This lane does not relax existing GUI/web/2D Vulkan RenderDoc gates or treat host readiness as Vulkan-backed browser proof.

## Cooperative Review
N/A for this slice: the current pass creates a scoped contract, detailed plan, and focused checks. Later implementation phases should split QEMU services, FPGA serial, Engine2D Vulkan, RenderDoc capture, and WM comparison into sidecars. Merge owner: Codex. Final reviewer: normal/highest-capability Codex verification. Shared interface names: `SimpleOsRuntimeProfile`, `profile_supports_capability`, `profile_requirement_status`, `simpleos_multiconfig_goal_status`. Manual step flow: `Load the SimpleOS runtime profiles`, `Validate FPGA serial-only behavior`, `Validate QEMU desktop service and GPU requirements`, `Read the Vulkan and RenderDoc completion contract`. Setup/checker helper: `test/01_unit/os/simpleos_config_matrix_spec.spl`. Fail-fast placeholders: future QEMU/RenderDoc wrappers must report `blocked:<reason>` until live evidence exists.

## Runtime Boundary Decision
- runtime_need: No new runtime capability is needed for the first contract slice.
- facade_checked: Existing pure Simple contract modules under `src/os/` and unit specs.
- chosen_path: reuse-facade.
- rejected_shortcuts: No raw `rt_*` aliases, no QEMU launch bypass, no fake RenderDoc `.rdc`, no screenshot-only Vulkan claim, and no FPGA non-serial capability fallback.

## Phase
dev-done

## Log
- impl: Hardened `src/app/repl/main.spl` for Windows bootstrap safety. The REPL
  now prefers concrete Windows release/bootstrap Simple binaries over the
  `bin/simple.exe` link and evaluates snippets with direct
  `process_run(simple_bin, ["run", temp])` through the `app.io.mod` facade
  instead of Unix-only `bash -c`, preventing the observed recursive
  `"bin/simple" src/app/repl/main.spl` process chain on Windows.
- impl: Fixed `scripts/check/check-vulkan-engine2d-readback.ps1` so
  `Invoke-SimpleWithTimeout` binds the argument array explicitly and refreshes
  the `Start-Process` process object before reading `ExitCode`. This keeps a
  successful Windows Simple launch/readback from being recorded as
  `evidence_exit_code=` / `evidence-program-failed`.
- verify: Stopped the runaway Windows REPL process chain and confirmed the
  environment returned to `simple.exe` process count `0`. Focused REPL checks
  passed with `src/compiler_rust/target/bootstrap/simple.exe check
  src/app/repl/main.spl`, and a noninteractive `--help` smoke exited `0`
  without leaving child `simple.exe` processes.
- verify: Real Engine2D Vulkan launch/readback on Windows passed with
  `powershell -NoProfile -ExecutionPolicy Bypass -File
  scripts\check\check-vulkan-engine2d-readback.ps1 -SimpleBinary
  src\compiler_rust\target\debug\simple.exe -WorkDir
  build\vulkan-engine2d-readback-real -EvidencePath
  build\simpleos_multiconfig_live_evidence\vulkan-engine2d-readback-real.env
  -TimeoutSeconds 180`. Evidence recorded `vulkan_probe_status=Initialized`,
  `backend_name=vulkan`, `present_exercised=true`,
  `readback_exercised=true`, zero clear/rect mismatches, matching rect checksum
  `140781974135910`, `vulkan_strict_exit_code=0`,
  `engine2d_cpu_vulkan_parity_exit_code=0`, and
  `vulkan_engine2d_readback_status=pass`.
- verify: Focused source check passed with
  `src/compiler_rust/target/debug/simple.exe check src/app/repl/main.spl
  scripts/check/check_simpleos_multiconfig_live_evidence.spl
  scripts/check/vulkan_engine2d_readback_evidence.spl
  src/os/simpleos_config_matrix.spl
  test/01_unit/os/simpleos_config_matrix_spec.spl`.
  Remaining full-goal blockers are still the real SimpleOS `.rdc` capture,
  QEMU/host RenderDoc log comparison, and any hardware-backed FPGA UART
  evidence not present on this Windows host.
- impl: Hardened `scripts/check/check-simpleos-qemu-rv64-desktop-evidence.ps1`
  live mode to capture QEMU stdout/stderr under
  `build/os/systest/qemu-riscv64-desktop/qemu.stdout.log` and
  `build/os/systest/qemu-riscv64-desktop/qemu.stderr.log`, emit
  `simpleos_qemu_rv64_stdout_path`,
  `simpleos_qemu_rv64_stderr_path`, and
  `simpleos_qemu_rv64_process_output_status`, and classify early nonzero QEMU
  exits as `blocked:qemu-exit-N` instead of a misleading boot timeout.
- impl: Extended
  `scripts/check/check_simpleos_multiconfig_live_evidence.spl` to echo the
  QEMU process-output rows from wrapper evidence.
- docs: Updated the detailed SimpleOS multi-config plan with the QEMU
  stdout/stderr diagnostics and the standalone Windows QEMU desktop-service
  live refresh command.
- verify: Initial QEMU live refresh with
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1 -RunLiveBoot -BootTimeoutSeconds 45 -KernelPath build/os/simpleos_riscv64_desktop_service.elf -EvidencePath build\simpleos_multiconfig_live_evidence\qemu-rv64-desktop-live-refresh.env`
  exposed a QEMU process failure; captured stderr showed
  `cannot set up guest memory 'virt.flash1': Invalid argument`. A follow-up
  rerun with the fixed exit-code handling then exited `0` and emitted
  `simpleos_qemu_rv64_live_boot_status=probed`,
  `simpleos_qemu_serial_console_status=pass`,
  `simpleos_qemu_rv64_ssh_banner=SSH-2.0-SimpleOS_1.0`,
  `simpleos_qemu_rv64_ssh_probe_status=pass`,
  `simpleos_qemu_rv64_http_status_code=200`,
  `simpleos_qemu_rv64_http_probe_status=pass`,
  `simpleos_qemu_gpu_readback_status=pass`,
  `simpleos_qemu_wm_marker_status=pass`, and
  `simpleos_qemu_rv64_blocker=pass`.
- verify: Aggregate follow-up over
  `build\simpleos_multiconfig_live_evidence\qemu-rv64-desktop-live-refresh.env`
  exited `1` as expected for a QEMU-only evidence file, but reported
  `simpleos_qemu_service_evidence_status=pass` and advanced the aggregate
  blocker to
  `simpleos_multiconfig_live_status=blocked:fpga-serial:blocked:missing-fpga-uart-terminal`.
- verify: Focused checks after QEMU live diagnostic hardening passed:
  `src\compiler_rust\target\debug\simple.exe check scripts\check\check_simpleos_multiconfig_live_evidence.spl scripts\check\vulkan_engine2d_readback_evidence.spl src\os\simpleos_config_matrix.spl test\01_unit\os\simpleos_config_matrix_spec.spl`;
  `$env:SIMPLE_LIB='src'; .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean`
  with 14 passing scenarios; generated-spec layout count `0`; and
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check`
  with `STATUS: PASS spipe-dev-command wiring`. `Get-Command sh` still failed
  in this Windows shell. Scoped `rt_*` search over the touched QEMU
  wrapper/checker/docs found no new raw runtime shortcuts; only older
  lane-state references remained.
- impl: Extended
  `scripts/check/check_simpleos_multiconfig_live_evidence.spl` so the
  operator-facing aggregate output now echoes `simpleos_wm_argb_diff_status`
  and `simpleos_wm_argb_mismatch_count` beside the existing ARGB reason.
- docs: Updated the detailed plan and WM compare guide with the refreshed live
  WM comparison artifact and the aggregate ARGB visibility rows.
- verify: Refreshed WM host/QEMU evidence from live QEMU service rows with
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-wm-host-compare-evidence.ps1 -BaseEvidencePath build\simpleos_multiconfig_live_evidence\qemu-rv64-desktop-live-refresh.env -EvidencePath build\simpleos_multiconfig_live_evidence\wm-host-compare-live-refresh.env -AttemptHostWmCapture -HostCaptureTimeoutSeconds 20`.
  The wrapper exited `1` as expected because RenderDoc logs are absent, but the
  bitmap parity rows passed: QEMU and host PPMs are both `320x240`, capture
  kinds are `qemu-wm-rect-scene` and `hosted-wm-rect-scene`, both scenes are
  `simpleos-desktop-four-windows`, titlebar/taskbar checks pass on both sides,
  `simpleos_wm_argb_diff_status=pass`, and
  `simpleos_wm_argb_mismatch_count=0`.
- verify: Aggregate follow-up over
  `build\simpleos_multiconfig_live_evidence\wm-host-compare-live-refresh.env`
  exited `1` as expected while reporting `simpleos_qemu_service_evidence_status=pass`,
  `simpleos_wm_argb_diff_status=pass`,
  `simpleos_wm_argb_mismatch_count=0`, and
  `simpleos_wm_structured_compare_evidence_status=blocked:missing-renderdoc-log-compare`.
  Remaining blockers are FPGA UART hardware evidence, SimpleOS Engine2D Vulkan
  backend/readback evidence, SimpleOS `.rdc` magic, and QEMU/host RenderDoc log
  comparison.
- impl: Extended
  `scripts/check/check_simpleos_multiconfig_live_evidence.spl` so Engine2D
  operator output now echoes bridge profile, drawing backend, processing
  backend, runtime backend, Vulkan device name, viewport, readback checksum,
  nonblank status, and QEMU GPU readback path/dimensions.
- docs: Updated the detailed plan and Windows Vulkan setup guide with the
  preflight-only Engine2D/RenderDoc refresh command and the distinction between
  passing QEMU framebuffer readback and missing SimpleOS Engine2D Vulkan
  backend proof.
- verify: Noninvasive Engine2D/RenderDoc refresh over
  `build\simpleos_multiconfig_live_evidence\wm-host-compare-live-refresh.env`
  with
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-engine2d-renderdoc-evidence.ps1 -BaseEvidencePath build\simpleos_multiconfig_live_evidence\wm-host-compare-live-refresh.env -EvidencePath build\simpleos_multiconfig_live_evidence\engine2d-renderdoc-live-preflight.env -RunSimpleVulkanProbe -SimpleVulkanProbePreflightOnly -AllowHighSimpleProcessCount -SimpleBinary bin\simple.exe -ProbeHostVulkan`
  exited `1` as expected without launching a Simple Vulkan child. It recorded
  `simpleos_qemu_gpu_readback_status=pass`, QEMU GPU dimensions `320x240`,
  `simpleos_windows_vulkaninfo_status=pass`,
  `simpleos_windows_vulkan_device_name=Intel(R) UHD Graphics 770`,
  `simpleos_engine2d_direct_readback_reason=preflight-only`,
  `simpleos_engine2d_direct_readback_existing_simple_process_count=25291`,
  `simpleos_engine2d_processing_backend=missing`, and
  `simpleos_engine2d_readback_nonblank_status=blocked:source-evidence-not-usable`.
- impl: Added `SimpleOsEngine2dSourceBridgeAudit` to
  `src/os/simpleos_config_matrix.spl` and a focused spec case that keeps the
  current QEMU Engine2D source wiring fail-closed until the desktop-service draw
  path is wired to the Vulkan Engine2D session.
- impl: Extended
  `scripts/check/check-simpleos-engine2d-renderdoc-evidence.ps1` to emit source
  audit rows for the QEMU desktop-service entry, freestanding baremetal
  Engine2D core, Engine2D VirtIO surface contract, Engine2D Vulkan session, the
  current draw path, the target processing backend, and the source audit status.
  The aggregate checker now echoes those rows.
- docs: Updated the detailed plan and Windows Vulkan setup guide with the
  source-audit rows and the distinction between source surfaces being present
  and the QEMU desktop-service path being wired to Vulkan Engine2D.
- verify: Source-audit refresh over live QEMU/WM evidence with
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-engine2d-renderdoc-evidence.ps1 -BaseEvidencePath build\simpleos_multiconfig_live_evidence\wm-host-compare-live-refresh.env -EvidencePath build\simpleos_multiconfig_live_evidence\engine2d-renderdoc-live-source-audit.env -RunSimpleVulkanProbe -SimpleVulkanProbePreflightOnly -AllowHighSimpleProcessCount -SimpleBinary bin\simple.exe -ProbeHostVulkan`
  exited `1` as expected and emitted `simpleos_engine2d_source_qemu_entry_status=pass`,
  `simpleos_engine2d_source_baremetal_core_status=pass`,
  `simpleos_engine2d_source_virtio_surface_status=pass`,
  `simpleos_engine2d_source_vulkan_session_status=pass`,
  `simpleos_engine2d_source_current_draw_path=freestanding-display-runtime`,
  `simpleos_engine2d_source_target_processing_backend=vulkan`, and
  `simpleos_engine2d_source_bridge_audit_status=blocked:desktop-service-not-wired-to-vulkan-engine2d-session`.
- verify: Focused source-audit checks passed with
  `src\compiler_rust\target\debug\simple.exe check scripts\check\check_simpleos_multiconfig_live_evidence.spl scripts\check\vulkan_engine2d_readback_evidence.spl src\os\simpleos_config_matrix.spl test\01_unit\os\simpleos_config_matrix_spec.spl`.
  The updated unit spec passed through the Rust debug binary with 15 scenarios:
  `$env:SIMPLE_LIB='src'; src\compiler_rust\target\debug\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean`.
  The same spec through `.\bin\simple.exe` failed during startup with
  `memory allocation of 29952 bytes failed` before test results, matching the
  current host process-pressure risk; it was not used as passing evidence.
- impl: Added opt-in bounded FPGA UART capture to
  `scripts/check/check-simpleos-fpga-rv64-serial-evidence.ps1`. The wrapper now
  accepts `-CaptureSerial`, `-CaptureTimeoutSeconds`, and `-CaptureBaudRate`,
  opens the configured `-SerialDevice`, writes the capture log, stops early
  when `SIMPLEOS_FPGA_RISCV64_SERIAL_BOOT` is seen, and emits
  `simpleos_fpga_serial_capture_*` rows. Missing device, missing log path,
  timeout, or open/read failures remain blocked and cannot promote UART
  evidence.
- impl: Added combined-wrapper passthrough
  `-CaptureFpgaSerial`, `-FpgaSerialDevice`,
  `-FpgaSerialCaptureTimeoutSeconds`, and `-FpgaSerialCaptureBaudRate` in
  `scripts/check/check-simpleos-multiconfig-live-evidence.ps1`.
- impl: Extended
  `scripts/check/check_simpleos_multiconfig_live_evidence.spl` to echo
  optional FPGA serial capture rows so the operator-facing aggregate output
  preserves live UART capture diagnostics.
- docs: Updated the detailed SimpleOS multi-config plan and Windows Vulkan
  setup guide with the FPGA UART capture commands and the rule that capture is
  bounded, opt-in, and still requires the boot marker plus toolchain/bitstream
  rows to pass.
- verify: No-hardware FPGA capture smoke
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-fpga-rv64-serial-evidence.ps1 -CaptureSerial -CaptureTimeoutSeconds 1 -EvidencePath build\simpleos_multiconfig_live_evidence\fpga-rv64-serial-capture-no-device.env`
  exited `1` as expected with
  `simpleos_fpga_serial_capture_status=blocked:missing-serial-device`,
  `simpleos_fpga_serial_capture_bytes=0`, and
  `simpleos_fpga_uart_terminal_status=blocked`.
- verify: Aggregate follow-up over
  `build\simpleos_multiconfig_live_evidence\fpga-rv64-serial-capture-no-device.env`
  exited `1` as expected and echoed the new
  `simpleos_fpga_serial_capture_*` rows while keeping
  `simpleos_fpga_serial_evidence_status=blocked:missing-fpga-uart-terminal`.
- verify: Supplied-log smoke using
  `build\simpleos_multiconfig_live_evidence\fpga-rv64-serial-synthetic.log`
  with `SIMPLEOS_FPGA_RISCV64_SERIAL_BOOT`, `SimpleOS RV64 boot OK`,
  `TEST PASSED`, `-SerialDevice COM_SYNTHETIC`, `-ToolchainStatus pass`, and
  `-BitstreamStatus pass` exited `0`; aggregate consumption of the resulting
  env reported `simpleos_fpga_serial_evidence_status=pass` while the full
  multi-config status stayed blocked on missing QEMU evidence for that
  FPGA-only file.
- verify: Focused checks after FPGA UART capture support passed:
  `src\compiler_rust\target\debug\simple.exe check scripts\check\check_simpleos_multiconfig_live_evidence.spl scripts\check\vulkan_engine2d_readback_evidence.spl src\os\simpleos_config_matrix.spl test\01_unit\os\simpleos_config_matrix_spec.spl`;
  `$env:SIMPLE_LIB='src'; .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean`
  with 14 passing scenarios; generated-spec layout count `0`; and
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check`
  with `STATUS: PASS spipe-dev-command wiring`. `Get-Command sh` still failed
  in this Windows shell. Scoped `rt_*` search over the touched wrapper/checker
  and docs found no new raw runtime shortcuts; only older lane-state references
  remained.
- impl: Added `scripts/check/check-simpleos-rdoc-raw-row-gate.ps1`, a
  Windows-native synthetic aggregate checker for the RDOC raw-row gate. It
  generates isolated evidence under
  `build/simpleos_multiconfig_live_evidence/rdoc-raw-row-gate/`, runs the
  aggregate checker twice, and exits `0` only when raw `RDOC` without
  `simpleos_renderdoc_rdc_magic_status=pass` remains blocked while raw `RDOC`
  with the explicit magic-status row passes.
- docs: Updated the detailed plan and WM compare guide to name the repeatable
  RDOC raw-row gate checker and to state that it is aggregate-contract smoke,
  not real SimpleOS `.rdc`/RenderDoc completion evidence.
- verify: `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-rdoc-raw-row-gate.ps1`
  exited `0` with
  `simpleos_rdoc_raw_row_gate_missing_status_exit_code=1`,
  `simpleos_rdoc_raw_row_gate_missing_status_artifact_status=blocked:missing-simple-rdoc-magic`,
  `simpleos_rdoc_raw_row_gate_missing_status_wm_status=blocked:missing-simple-rdoc-magic`,
  `simpleos_rdoc_raw_row_gate_with_status_exit_code=0`,
  `simpleos_rdoc_raw_row_gate_with_status_artifact_status=pass`,
  `simpleos_rdoc_raw_row_gate_with_status_wm_status=pass`, and
  `simpleos_rdoc_raw_row_gate_status=pass`.
- verify: Focused checks after adding the repeatable RDOC raw-row gate passed:
  `src\compiler_rust\target\debug\simple.exe check scripts\check\check_simpleos_multiconfig_live_evidence.spl scripts\check\vulkan_engine2d_readback_evidence.spl src\os\simpleos_config_matrix.spl test\01_unit\os\simpleos_config_matrix_spec.spl`;
  `$env:SIMPLE_LIB='src'; .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean`
  with 14 passing scenarios; generated-spec layout count `0`; and
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check`
  with `STATUS: PASS spipe-dev-command wiring`. `Get-Command sh` still failed
  on this Windows shell. Repeated `.gitconfig` lock warnings were environmental
  noise.
- impl: Tightened raw-row derivation in
  `scripts/check/check_simpleos_multiconfig_live_evidence.spl` so RenderDoc
  artifact evidence requires both `simpleos_renderdoc_rdc_magic=RDOC` and
  `simpleos_renderdoc_rdc_magic_status=pass`; WM-RenderDoc evidence now keys
  off `simpleos_renderdoc_rdc_magic_status=pass`.
- docs: Updated the detailed plan, WM compare guide, and generated/manual spec
  mirror to state that raw `RDOC` magic alone is not sufficient for aggregate
  raw-row ingestion.
- verify: Synthetic aggregate evidence
  `build/simpleos_multiconfig_live_evidence/rdoc-raw-missing-status.env`
  contained raw `simpleos_renderdoc_rdc_magic=RDOC` but no magic-status row and
  exited `1` with
  `simpleos_renderdoc_artifact_evidence_status=blocked:missing-simple-rdoc-magic`
  and `simpleos_wm_renderdoc_evidence_status=blocked:missing-simple-rdoc-magic`.
- verify: Synthetic aggregate evidence
  `build/simpleos_multiconfig_live_evidence/rdoc-raw-with-status.env` included
  `simpleos_renderdoc_rdc_magic_status=pass` and exited `0` with both
  RenderDoc-derived statuses and `simpleos_multiconfig_live_status=pass`.
- verify: Focused checks after tightening RDOC raw-row derivation passed:
  `src\compiler_rust\target\debug\simple.exe check scripts\check\check_simpleos_multiconfig_live_evidence.spl scripts\check\vulkan_engine2d_readback_evidence.spl src\os\simpleos_config_matrix.spl test\01_unit\os\simpleos_config_matrix_spec.spl`;
  `$env:SIMPLE_LIB='src'; .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean`
  with 14 cached passing scenarios; generated-spec layout count `0`; and
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check`
  with `STATUS: PASS spipe-dev-command wiring`. `Get-Command sh` still failed.
- impl: Replaced stale `simpleos_engine2d_vulkan_backend_status` in
  `simpleos_wm_renderdoc_required_evidence_keys()` with the wrapper-emitted
  `simpleos_renderdoc_simple_runtime_backend` and
  `simpleos_renderdoc_simple_scene` rows.
- spec: Updated the focused SimpleOS multi-config spec to assert the emitted
  WM-RenderDoc runtime backend and scene keys.
- docs: Updated the detailed plan and generated/manual spec mirror so the
  WM-RenderDoc gate refers to emitted RenderDoc runtime/scene rows instead of
  a non-emitted backend-status alias.
- verify: Aggregate no-artifact smoke printed
  `simpleos_wm_renderdoc_required_evidence_keys=simpleos_renderdoc_rdc_magic_status,simpleos_renderdoc_simple_runtime_backend,simpleos_renderdoc_simple_scene,...`
  and kept
  `simpleos_multiconfig_live_status=blocked:qemu-service:blocked:missing-qemu-serial-console`.
- verify: Scoped search for `simpleos_engine2d_vulkan_backend_status` across
  the lane-owned source/spec/checker/docs returned no matches.
- verify: Focused checks after the WM-RenderDoc key alignment passed:
  `src\compiler_rust\target\debug\simple.exe check scripts\check\check_simpleos_multiconfig_live_evidence.spl scripts\check\vulkan_engine2d_readback_evidence.spl src\os\simpleos_config_matrix.spl test\01_unit\os\simpleos_config_matrix_spec.spl`;
  `$env:SIMPLE_LIB='src'; .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean`
  with 14 passing scenarios; generated-spec layout count `0`; and
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check`
  with `STATUS: PASS spipe-dev-command wiring`. `Get-Command sh` still failed.
- impl: Added `simpleos_renderdoc_rdc_magic_status` to
  `simpleos_renderdoc_artifact_required_evidence_keys()` so the typed
  artifact-level contract now matches the Windows wrapper output and the
  evidence table, while still retaining raw `simpleos_renderdoc_rdc_magic`.
- spec: Extended the focused SimpleOS multi-config spec to assert that
  RenderDoc artifact required keys include
  `simpleos_renderdoc_rdc_magic_status`.
- docs: Updated the generated/manual spec mirror and SimpleOS multi-config TLDR
  to name both the raw RDOC magic row and the explicit magic-status row.
- impl: Extended `scripts/check/check_simpleos_multiconfig_live_evidence.spl`
  to print `simpleos_renderdoc_artifact_required_evidence_keys` and
  `simpleos_wm_renderdoc_required_evidence_keys` beside the six live aggregate
  keys, making the RDOC magic/status and WM RenderDoc requirements visible in
  blocked operator output.
- docs: Updated the detailed plan and generated/manual spec mirror to document
  the new aggregate required-key rows.
- verify: Aggregate no-artifact smoke
  `SIMPLE_LIB=src src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --mode=interpreter`
  exited `1` as expected and printed
  `simpleos_renderdoc_artifact_required_evidence_keys=...simpleos_renderdoc_rdc_magic_status...`,
  `simpleos_wm_renderdoc_required_evidence_keys=...simpleos_renderdoc_rdc_magic_status...`,
  and `simpleos_multiconfig_live_status=blocked:qemu-service:blocked:missing-qemu-serial-console`.
- verify: Focused checks after the artifact-key alignment passed:
  `src\compiler_rust\target\debug\simple.exe check scripts\check\check_simpleos_multiconfig_live_evidence.spl scripts\check\vulkan_engine2d_readback_evidence.spl src\os\simpleos_config_matrix.spl test\01_unit\os\simpleos_config_matrix_spec.spl`;
  `$env:SIMPLE_LIB='src'; .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean`
  with 14 cached passing scenarios; generated-spec layout count `0`; and
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check`
  with `STATUS: PASS spipe-dev-command wiring`. `Get-Command sh` still failed.
- impl: Fixed `scripts/check/check-simpleos-engine2d-renderdoc-evidence.ps1`
  so `simpleos_engine2d_readback_nonblank_status` is computed after source
  usability is derived. Direct Simple Vulkan evidence can no longer be
  classified from an uninitialized usability record.
- impl: Added the explicit `simpleos_renderdoc_rdc_magic_status` row to both
  Windows RenderDoc evidence wrappers and aggregate output while retaining
  `simpleos_renderdoc_rdc_status` as the compatibility row.
- docs: Updated the WM compare guide to document that the Windows wrappers now
  emit both RDOC status rows and keep them fail-closed for missing or malformed
  `.rdc` files.
- verify: Engine2D/RenderDoc wrapper smoke
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-engine2d-renderdoc-evidence.ps1 -EvidencePath build\simpleos_multiconfig_live_evidence\engine2d-renderdoc-rdoc-status.env -BaseEvidencePath build\simpleos_multiconfig_live_evidence\wm-host-compare.env`
  exited `1` as expected with
  `simpleos_engine2d_readback_nonblank_status=blocked:source-evidence-not-usable`,
  `simpleos_renderdoc_rdc_magic_status=missing`, and
  `simpleos_renderdoc_rdc_status=missing`.
- verify: WM wrapper smoke over
  `build\simpleos_multiconfig_live_evidence\wm-host-compare-rdoc-status.env`
  exited `1` as expected and emitted both RDOC status rows plus
  `simpleos_wm_renderdoc_log_compare_status=missing`.
- verify: Aggregate follow-up over
  `build/simpleos_multiconfig_live_evidence/engine2d-renderdoc-rdoc-status.env`
  exited `1` as expected and echoed
  `simpleos_renderdoc_rdc_magic_status=missing`,
  `simpleos_renderdoc_rdc_status=missing`, and
  `simpleos_multiconfig_live_status=blocked:qemu-service:blocked:missing-qemu-serial-console`.
- verify: Focused checks after the RDOC status-row fix passed:
  `src\compiler_rust\target\debug\simple.exe check scripts\check\check_simpleos_multiconfig_live_evidence.spl scripts\check\vulkan_engine2d_readback_evidence.spl src\os\simpleos_config_matrix.spl test\01_unit\os\simpleos_config_matrix_spec.spl`;
  `$env:SIMPLE_LIB='src'; .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean`
  with 14 cached passing scenarios; generated-spec layout count `0`; and
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check`
  with `STATUS: PASS spipe-dev-command wiring`. `Get-Command sh` still failed.
- impl: Added diagnostic Windows FPGA serial-port inventory to
  `scripts/check/check-simpleos-fpga-rv64-serial-evidence.ps1`. The wrapper now
  supports `-ProbeSerialPorts`, writes `simpleos_fpga_serial_port_probe_*`,
  `simpleos_fpga_serial_device_candidate_status`, and
  `simpleos_fpga_serial_inventory_evidence_status=diagnostic`, and produces a
  sidecar `fpga-rv64-serial-ports.env` without treating COM-port presence as a
  UART boot pass.
- impl: Added `-ProbeFpgaSerialPorts` passthrough to the combined Windows
  multi-config wrapper and aggregate printing for the FPGA serial inventory
  rows.
- docs: Updated the SimpleOS multi-config Vulkan/WM plan and Windows
  GUI/Web/2D Vulkan setup guide with the FPGA serial inventory command and the
  rule that a real serial log boot marker is still required.
- verify: FPGA serial-port inventory smoke
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-fpga-rv64-serial-evidence.ps1 -ProbeSerialPorts`
  exited `1` as expected with
  `simpleos_fpga_serial_port_probe_status=missing`,
  `simpleos_fpga_serial_port_probe_count=0`,
  `simpleos_fpga_serial_inventory_evidence_status=diagnostic`, and
  `simpleos_fpga_uart_terminal_status=blocked`.
- verify: Aggregate follow-up over
  `build/simpleos_multiconfig_live_evidence/fpga-rv64-serial.env` exited `1`
  as expected, echoed the FPGA serial inventory rows, and kept
  `simpleos_fpga_serial_evidence_status=blocked:missing-fpga-uart-terminal`.
- verify: Combined Windows wrapper smoke with
  `-ProbeFpgaSerialPorts -SkipAggregate` forwarded the inventory probe and
  wrote `simpleos_multiconfig_windows_wrapper_fpga_serial_port_inventory_path`
  while keeping the wrapper aggregate status skipped/nonpassing.
- verify: Focused checks after the FPGA inventory integration passed:
  `src\compiler_rust\target\debug\simple.exe check scripts\check\check_simpleos_multiconfig_live_evidence.spl scripts\check\vulkan_engine2d_readback_evidence.spl src\os\simpleos_config_matrix.spl test\01_unit\os\simpleos_config_matrix_spec.spl`;
  `$env:SIMPLE_LIB='src'; .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean`
  with 14 cached passing scenarios; generated-spec layout count `0`; and
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check`
  with `STATUS: PASS spipe-dev-command wiring`. `Get-Command sh` still failed.
- impl: Added `-HostCaptureTimeoutSeconds` to the combined Windows evidence
  wrapper and forwarded it to the focused WM host-capture wrapper whenever
  `-AttemptHostWmCapture` is requested. The combined wrapper now exposes the
  same bounded hosted-WM capture control as
  `scripts/check/check-simpleos-wm-host-compare-evidence.ps1`.
- docs: Updated the detailed SimpleOS multi-config/Vulkan/WM plan with the
  combined wrapper timeout passthrough and the current-source Windows refresh
  command that rebuilds QEMU desktop and FPGA serial kernels, runs live QEMU,
  attempts hosted-WM capture, and records host Vulkan diagnostics.
- verify: Combined Windows current-source refresh on 2026-06-26:
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-multiconfig-live-evidence.ps1 -BuildDesktopServiceKernel -BuildFpgaSerialKernel -AttemptHostWmCapture -HostCaptureTimeoutSeconds 20 -ProbeHostVulkan -BuildBackend cranelift -BuildCc C:\dev\install\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin\clang.exe -RunLiveBoot -BootTimeoutSeconds 45`
  exited `1` as expected. QEMU child exit was `0`, QEMU service evidence
  passed, FPGA serial build rows passed while UART evidence remained missing,
  hosted-WM capture passed through `hosted-wm-capture-stdout-ppm`, QEMU/host
  captures both classified as 320x240 rectangle scenes with ARGB diff `pass`,
  Windows Vulkan discovery passed, SDK tools and RenderDoc remained missing,
  and aggregate status remained
  `blocked:fpga-serial:blocked:missing-fpga-uart-terminal`.
- verify: Focused guards after the wrapper change passed:
  `src\compiler_rust\target\debug\simple.exe check scripts\check\check_simpleos_multiconfig_live_evidence.spl src\os\simpleos_config_matrix.spl test\01_unit\os\simpleos_config_matrix_spec.spl`;
  `$env:SIMPLE_LIB='src'; .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean`
  with 14 passing cached scenarios; generated-spec layout count `0`; and
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check`
  with `STATUS: PASS spipe-dev-command wiring`. `Get-Command sh` still failed,
  so Unix `direct-env-runtime-guard.shs` audits remain unavailable in this
  Windows PowerShell environment.
- impl: Added Windows-native Simple Vulkan Engine2D readback evidence support.
  `scripts/check/vulkan_engine2d_readback_evidence.spl` contains the direct
  clear/rect/present/readback evidence program, and
  `scripts/check/check-vulkan-engine2d-readback.ps1` runs it, writes
  `vulkan_engine2d_readback_*` rows, and runs the existing strict/parity specs
  when the direct evidence passes.
- impl: Extended `scripts/check/check-simpleos-engine2d-renderdoc-evidence.ps1`
  to consume direct `vulkan_engine2d_readback_*` rows, expose
  `simpleos_engine2d_direct_readback_status`, reason, and exit code, and avoid
  marking Engine2D readback nonblank as pass when the Simple source evidence is
  unusable. Added `-RunSimpleVulkanProbe` passthrough there and in the combined
  Windows wrapper.
- docs: Updated the Windows Vulkan setup guide and SimpleOS multi-config plan
  with the native PowerShell Simple Vulkan probe commands and fail-closed
  timeout interpretation.
- verify: `src\compiler_rust\target\debug\simple.exe check scripts\check\vulkan_engine2d_readback_evidence.spl`
  passed. A short Windows smoke run
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-vulkan-engine2d-readback.ps1 -SimpleBinary bin\simple.exe -WorkDir build\vulkan-engine2d-readback-windows-timeout-smoke -TimeoutSeconds 5`
  exited `1` with `vulkan_engine2d_readback_reason=evidence-program-timeout`
  and direct evidence exit code `124`.
- verify: The Engine2D/RenderDoc wrapper with `-RunSimpleVulkanProbe` and a
  five-second timeout propagated that evidence as
  `simpleos_engine2d_direct_readback_reason=evidence-program-timeout`,
  `simpleos_engine2d_source_evidence_usable_reason=direct-simple-vulkan-readback-evidence-program-timeout`,
  and `simpleos_engine2d_readback_nonblank_status=blocked:source-evidence-not-usable`.
- impl: Hardened `scripts/check/check-vulkan-engine2d-readback.ps1` with a
  preflight process-count guard and file-redirect child capture. By default the
  wrapper stops before launching another Simple child when more than 128
  `simple.exe` processes already exist, emits
  `vulkan_engine2d_readback_reason=existing-simple-process-count-high`, and
  records the count/limit rows. `-AllowHighSimpleProcessCount` is available for
  deliberate override after the operator accepts that host state.
- impl: Propagated the direct Simple process-count rows through
  `scripts/check/check-simpleos-engine2d-renderdoc-evidence.ps1`, the combined
  Windows wrapper, and the aggregate checker as
  `simpleos_engine2d_direct_readback_existing_simple_process_count` and
  `simpleos_engine2d_direct_readback_existing_simple_process_limit`.
- verify: On the current Windows host,
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-vulkan-engine2d-readback.ps1 -SimpleBinary bin\simple.exe -WorkDir build\vulkan-engine2d-readback-process-guard-smoke -TimeoutSeconds 20`
  exited `1` without launching the Simple Vulkan child and reported
  `vulkan_engine2d_readback_existing_simple_process_count=23534` with limit
  `128`.
- verify: The Engine2D/RenderDoc wrapper with `-RunSimpleVulkanProbe` now
  reports `simpleos_engine2d_direct_readback_reason=existing-simple-process-count-high`,
  `simpleos_engine2d_direct_readback_existing_simple_process_count=23562`, and
  `simpleos_engine2d_source_evidence_usable_reason=direct-simple-vulkan-readback-existing-simple-process-count-high`.
  The aggregate checker echoes the same direct-process rows.
- impl: Added `-PreflightOnly` to
  `scripts/check/check-vulkan-engine2d-readback.ps1` and
  `-SimpleVulkanProbePreflightOnly` passthroughs to the Engine2D/RenderDoc and
  combined Windows wrappers. This records direct Simple process state without
  launching a Simple Vulkan evidence child.
- verify: Direct preflight-only run
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-vulkan-engine2d-readback.ps1 -SimpleBinary bin\simple.exe -WorkDir build\vulkan-engine2d-readback-preflight-only -PreflightOnly -AllowHighSimpleProcessCount`
  exited `1` as expected with `vulkan_engine2d_readback_status=blocked`,
  `vulkan_engine2d_readback_reason=preflight-only`, and
  `vulkan_engine2d_readback_existing_simple_process_count=23679`.
- verify: The Engine2D/RenderDoc wrapper preflight-only path propagated
  `simpleos_engine2d_direct_readback_reason=preflight-only`,
  `simpleos_engine2d_direct_readback_preflight_only=true`, and
  `simpleos_engine2d_direct_readback_existing_simple_process_count=23686`; the
  aggregate checker echoed the same rows.
- impl: Added `scripts/check/check-simple-process-inventory.ps1`, a
  dry-run-first Windows helper that writes `simple_process_inventory_*` rows,
  samples bounded PIDs/ages, and requires
  `-Kill -ConfirmText KILL_SIMPLE_PROCESSES` before terminating any
  `simple.exe` process.
- impl: Added `-RunSimpleProcessInventory` to the combined Windows wrapper and
  aggregate printing for the inventory rows, so the merged SimpleOS evidence can
  carry process-state blockers without launching the Simple Vulkan child.
- verify: Dry-run inventory command
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simple-process-inventory.ps1 -EvidencePath build\simpleos_multiconfig_live_evidence\simple-process-inventory.env -MaxSample 10`
  exited `1` as expected with
  `simple_process_inventory_status=blocked:process-count-over-limit`,
  `simple_process_inventory_count=23785`, and
  `simple_process_inventory_kill_requested=false`.
- verify: Aggregate checker over
  `build\simpleos_multiconfig_live_evidence\simple-process-inventory.env`
  echoed the `simple_process_inventory_*` rows, including sample PIDs and ages.
- verify: Focused checks after adding the inventory helper passed:
  `src\compiler_rust\target\debug\simple.exe check scripts\check\check_simpleos_multiconfig_live_evidence.spl scripts\check\vulkan_engine2d_readback_evidence.spl src\os\simpleos_config_matrix.spl test\01_unit\os\simpleos_config_matrix_spec.spl`;
  `$env:SIMPLE_LIB='src'; .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean`
  with 14 cached passing scenarios; generated-spec layout count `0`; and
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check`
  with `STATUS: PASS spipe-dev-command wiring`. `Get-Command sh` still failed.
- verify: Focused checks after the preflight-only integration passed:
  `src\compiler_rust\target\debug\simple.exe check scripts\check\vulkan_engine2d_readback_evidence.spl scripts\check\check_simpleos_multiconfig_live_evidence.spl src\os\simpleos_config_matrix.spl test\01_unit\os\simpleos_config_matrix_spec.spl`;
  `$env:SIMPLE_LIB='src'; .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean`
  with 14 cached passing scenarios; generated-spec layout count `0`; and
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check`
  with `STATUS: PASS spipe-dev-command wiring`. `Get-Command sh` still failed.
- verify: Focused checks after the Windows direct-probe integration passed:
  `src\compiler_rust\target\debug\simple.exe check scripts\check\vulkan_engine2d_readback_evidence.spl scripts\check\check_simpleos_multiconfig_live_evidence.spl src\os\simpleos_config_matrix.spl test\01_unit\os\simpleos_config_matrix_spec.spl`;
  `$env:SIMPLE_LIB='src'; .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean`
  with 14 cached passing scenarios; generated-spec layout count `0`; and
  `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check`
  with `STATUS: PASS spipe-dev-command wiring`. `Get-Command sh` still failed,
  so Unix runtime/env audits remain unavailable from this Windows PowerShell
  session.
- impl: Hardened `scripts/check/check-simpleos-wm-host-compare-evidence.ps1`
  RenderDoc log comparison. `simpleos_wm_renderdoc_log_compare_status` now
  requires structured matching QEMU/host log fields instead of merely checking
  that both log files are nonempty.
- impl: The WM wrapper now parses QEMU/host RenderDoc log fields for
  `simpleos_wm_compare_scene`, `simpleos_renderdoc_simple_runtime_backend`,
  `simpleos_renderdoc_capture_mode`, and `simpleos_renderdoc_rdc_magic`, then
  emits `simpleos_wm_renderdoc_log_compare_reason`,
  `simpleos_wm_renderdoc_log_compare_mode`,
  `simpleos_wm_renderdoc_qemu_log_status`,
  `simpleos_wm_renderdoc_host_log_status`,
  `simpleos_wm_renderdoc_qemu_log_scene`,
  `simpleos_wm_renderdoc_host_log_scene`,
  `simpleos_wm_renderdoc_qemu_log_backend`, and
  `simpleos_wm_renderdoc_host_log_backend`.
- impl: Extended `scripts/check/check_simpleos_multiconfig_live_evidence.spl`
  to echo the structured RenderDoc log comparison rows in aggregate output.
- docs: Updated `doc/07_guide/app/ui/wm_compare.md` and
  `doc/03_plan/os/simpleos_multiconfig_vulkan_wm_plan.md` with the
  structured-log contract; nonempty QEMU/host log files alone are no longer
  sufficient evidence.
- verify: Real WM wrapper run with default missing RenderDoc log paths exited
  `1` as expected and emitted
  `simpleos_wm_renderdoc_log_compare_status=missing`,
  `simpleos_wm_renderdoc_log_compare_reason=missing-qemu-and-host-renderdoc-logs`,
  and `simpleos_wm_renderdoc_log_compare_mode=structured-renderdoc-log-compare`,
  while keeping QEMU/host WM ARGB diff passing with mismatch count `0`.
- verify: Aggregate follow-up over
  `build\simpleos_multiconfig_live_evidence\wm-host-compare.env` exited `1`
  as expected and now echoes the structured RenderDoc log comparison rows.
- verify: Temporary structured probe logs under `build/os/systest/qemu-riscv64-desktop`
  with matching scene, Vulkan backend, `capture-simple`, and `RDOC` fields made
  `simpleos_wm_renderdoc_log_compare_status=pass` and
  `simpleos_wm_qemu_host_compare_status=pass`; the wrapper still exited `1`
  because the real SimpleOS `.rdc` artifact was absent. The temporary probe
  logs were removed and the real missing-log evidence file was restored.
- impl: Hardened `scripts/check/check-simpleos-engine2d-renderdoc-evidence.ps1`
  so stale GUI/browser setup output cannot masquerade as SimpleOS Engine2D
  Vulkan proof. The wrapper now emits source-usability rows:
  `simpleos_engine2d_source_evidence_mode`,
  `simpleos_engine2d_source_simple_status`,
  `simpleos_engine2d_source_browser_backing_status`,
  `simpleos_engine2d_source_evidence_usable_status`,
  `simpleos_engine2d_source_evidence_usable_reason`, and
  `simpleos_engine2d_runtime_backend_reason`.
- impl: Added RenderDoc blocker diagnostics to the same wrapper:
  `simpleos_renderdoc_rdc_status`,
  `simpleos_renderdoc_artifact_blocker_reason`, and
  `simpleos_wm_renderdoc_log_compare_reason`.
- impl: Extended `scripts/check/check_simpleos_multiconfig_live_evidence.spl`
  so the aggregate checker echoes those source-usability and RenderDoc blocker
  rows beside the existing six live gates.
- docs: Updated `doc/03_plan/os/simpleos_multiconfig_vulkan_wm_plan.md` and
  `doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md` with the new row contract
  and the rule that `--browser-backing` evidence with Simple not run is
  diagnostic only.
- verify: `powershell -NoProfile -ExecutionPolicy Bypass -File
  scripts\check\check-simpleos-engine2d-renderdoc-evidence.ps1
  -BaseEvidencePath build\simpleos_multiconfig_live_evidence\wm-host-compare.env
  -ProbeHostVulkan` exited `1` as expected and now reports
  `simpleos_engine2d_source_evidence_mode=--browser-backing`,
  `simpleos_engine2d_source_simple_status=not-run`,
  `simpleos_engine2d_source_evidence_usable_status=blocked`,
  `simpleos_engine2d_source_evidence_usable_reason=source-browser-backing-only-simple-not-run`,
  `simpleos_engine2d_runtime_backend_reason=simple-vulkan-probe-not-run`,
  `simpleos_renderdoc_rdc_status=missing`,
  `simpleos_renderdoc_artifact_blocker_reason=missing-simple-rdoc-magic`, and
  `simpleos_wm_renderdoc_log_compare_reason=missing-qemu-and-host-renderdoc-logs`.
- verify: Aggregate follow-up over
  `build\simpleos_multiconfig_live_evidence\engine2d-renderdoc.env` exited `1`
  as expected, echoed the new reason rows, kept QEMU service evidence passing,
  kept WM ARGB parity rows passing, and left Engine2D Vulkan / RenderDoc gates
  blocked without promoting host/browser diagnostics.
- verify: `src\compiler_rust\target\debug\simple.exe check
  scripts\check\check_simpleos_multiconfig_live_evidence.spl
  src\os\simpleos_config_matrix.spl` passed.
- impl: Replaced the RV64 virtio-gpu display flush pattern with a deterministic
  320x240 WM rectangle scene in
  `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`. The desktop
  service now flushes a titlebar/taskbar/content scene through the existing
  `rt_display_flush_test()` owner path instead of the old gradient pattern.
- impl: Changed `src/os/compositor/hosted_wm_capture_evidence.spl` stdout
  capture mode from slow full P3 pixel output to a marker-delimited compact
  rectangle scene. The Windows WM wrapper materializes that compact host scene
  as a P6 `host-wm.ppm`, avoiding the hosted file-output runtime path and the
  interpreter stdout timeout.
- impl: Extended `scripts/check/check-simpleos-wm-host-compare-evidence.ps1`
  to materialize `SIMPLE_WM_RECT_PPM_V1` stdout captures and classify the
  matching full-scene artifacts as `qemu-wm-rect-scene` and
  `hosted-wm-rect-scene`.
- docs: Updated the WM compare guide and SimpleOS multi-config Vulkan/WM plan
  to document the compact stdout scene, the `qemu-wm-rect-scene` /
  `hosted-wm-rect-scene` capture kinds, and the current zero-mismatch ARGB
  state that remains blocked only by missing RenderDoc log comparison.
- verify: `src\compiler_rust\target\debug\simple.exe check
  src\os\compositor\hosted_wm_capture_evidence.spl
  test\01_unit\os\compositor\hosted_wm_capture_evidence_spec.spl` passed.
- verify: `SIMPLE_LIB=src .\bin\simple.exe test
  test\01_unit\os\compositor\hosted_wm_capture_evidence_spec.spl
  --mode=interpreter --clean` passed 2 tests through the cache.
- verify: Host capture preflight against a stale QEMU screendump completed
  quickly with host PPM `320x240` and `simpleos_wm_host_capture_kind=hosted-wm-rect-scene`;
  QEMU still classified as `qemu-virtio-gpu-test-pattern` until the QEMU
  screendump was refreshed.
- verify: `powershell -NoProfile -ExecutionPolicy Bypass -File
  scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1
  -BuildDesktopServiceKernel -BuildBackend cranelift -BuildCc
  C:\dev\install\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin\clang.exe
  -RunLiveBoot -BootTimeoutSeconds 45` passed, including QMP screendump,
  SSH probe, HTTP probe, GPU readback, and WM marker rows.
- verify: `powershell -NoProfile -ExecutionPolicy Bypass -File
  scripts\check\check-simpleos-wm-host-compare-evidence.ps1
  -BaseEvidencePath build\simpleos_multiconfig_live_evidence\qemu-rv64-desktop.env
  -AttemptHostWmCapture -HostCaptureTimeoutSeconds 20` exited `1` as expected,
  with QEMU kind `qemu-wm-rect-scene`, host kind `hosted-wm-rect-scene`,
  scene/window/focus/titlebar/taskbar rows passing, `simpleos_wm_argb_diff_status=pass`,
  `simpleos_wm_argb_mismatch_count=0`, and the compare still missing only
  RenderDoc log comparison / SimpleOS `.rdc` evidence.
- verify: Aggregate follow-up over
  `build\simpleos_multiconfig_live_evidence\wm-host-compare.env` exited `1`
  as expected and now derives
  `simpleos_wm_structured_compare_evidence_status=blocked:missing-renderdoc-log-compare`.
- impl: Hardened `scripts/check/check-simpleos-wm-host-compare-evidence.ps1`
  so nonblank PPMs are classified before being promoted to structured WM scene
  rows. The wrapper now emits QEMU/host PPM dimensions, capture kinds, and
  `simpleos_wm_argb_diff_reason`; it detects the current RV64 screendump as
  `qemu-virtio-gpu-test-pattern` and the hosted stdout artifact as
  `hosted-wm-diagnostic-crop`.
- impl: Kept the WM gate fail-closed by no longer marking scene/window/focus,
  titlebar, or taskbar rows as pass when the artifacts are a GPU test pattern
  or diagnostic crop. GPU readback and host capture diagnostics still emit
  useful rows, but structured WM comparison remains blocked until comparable
  full-scene WM artifacts exist.
- impl: Extended
  `scripts/check/check_simpleos_multiconfig_live_evidence.spl` to echo the WM
  PPM dimensions, capture-kind rows, and ARGB diff reason from raw evidence
  files.
- docs: Updated `doc/03_plan/os/simpleos_multiconfig_vulkan_wm_plan.md` and
  `doc/07_guide/app/ui/wm_compare.md` with the capture-kind contract and the
  current `qemu-gpu-test-pattern-not-wm-scene` blocker.
- verify: `powershell -NoProfile -ExecutionPolicy Bypass -File
  scripts\check\check-simpleos-wm-host-compare-evidence.ps1
  -BaseEvidencePath build\simpleos_multiconfig_live_evidence\qemu-rv64-desktop.env
  -AttemptHostWmCapture -HostCaptureTimeoutSeconds 10` exited `1` as expected,
  with QEMU PPM `320x240`, QEMU kind `qemu-virtio-gpu-test-pattern`, host PPM
  `16x16`, host kind `hosted-wm-diagnostic-crop`,
  `simpleos_wm_argb_diff_reason=qemu-gpu-test-pattern-not-wm-scene`, and
  QEMU/host structured WM rows missing.
- verify: `src\compiler_rust\target\debug\simple.exe check
  scripts\check\check_simpleos_multiconfig_live_evidence.spl
  src\os\simpleos_config_matrix.spl
  test\01_unit\os\simpleos_config_matrix_spec.spl` passed.
- verify: `SIMPLE_LIB=src .\bin\simple.exe test
  test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean`
  passed 14 tests through the cache.
- verify: Aggregate follow-up over
  `build\simpleos_multiconfig_live_evidence\wm-host-compare.env` exited `1`
  as expected, echoed the new capture-kind diagnostics, and derived
  `simpleos_wm_structured_compare_evidence_status=blocked:missing-qemu-wm-scene`.
- impl: Hardened `scripts/check/check-simpleos-wm-host-compare-evidence.ps1`
  host capture execution. The wrapper now invokes the Simple entrypoint
  directly instead of the invalid `simple.exe run <entry>` form, bounds it with
  `-HostCaptureTimeoutSeconds`, redirects stdout/stderr to the capture log, and
  uses the entrypoint's marker-delimited stdout PPM mode to persist a host PPM
  without relying on the hosted file-output runtime path.
- impl: Fixed hosted framebuffer text drawing in
  `hosted_wm_capture_evidence.spl` and `shared_mdi_framebuffer_scene.spl` to use
  bounded index-based `char_code_at` loops. Added focused coverage in
  `test/01_unit/os/compositor/hosted_wm_capture_evidence_spec.spl` proving
  hosted text drawing and nonblank capture metrics without file output.
- impl: Extended the WM host-compare wrapper PPM reader to accept P3 host
  diagnostic captures as well as QEMU P6 captures, normalizing both to RGB bytes
  before exact comparison.
- impl: Added `SIMPLE_HOSTED_WM_CAPTURE_STDOUT_PPM=1` support to
  `hosted_wm_capture_evidence.spl`. The entrypoint emits
  `SIMPLE_HOSTED_WM_PPM_BEGIN` / `SIMPLE_HOSTED_WM_PPM_END` around a P3 crop of
  the hosted WM frame, while normal metrics still report the hosted renderer
  backend/readback status.
- verify: `src\compiler_rust\target\debug\simple.exe check
  src\os\compositor\hosted_wm_capture_evidence.spl
  test\01_unit\os\compositor\hosted_wm_capture_evidence_spec.spl` passed.
- verify: `SIMPLE_LIB=src .\bin\simple.exe test
  test\01_unit\os\compositor\hosted_wm_capture_evidence_spec.spl
  --mode=interpreter --clean` passed.
- verify: Earlier timeout diagnostic: `powershell -ExecutionPolicy Bypass -File
  scripts\check\check-simpleos-wm-host-compare-evidence.ps1
  -BaseEvidencePath build\simpleos_multiconfig_live_evidence\qemu-rv64-desktop.env
  -AttemptHostWmCapture -HostCaptureTimeoutSeconds 5` exited `1` with QEMU PPM
  still passing, hosted capture status
  `blocked:host-capture-timeout-5s`, host PPM missing, and structured WM compare
  still blocked on the missing host scene.
- verify: Updated stdout PPM diagnostic: `powershell -ExecutionPolicy Bypass
  -File scripts\check\check-simpleos-wm-host-compare-evidence.ps1
  -BaseEvidencePath build\simpleos_multiconfig_live_evidence\qemu-rv64-desktop.env
  -AttemptHostWmCapture -HostCaptureTimeoutSeconds 10` exited `1` with
  `simpleos_host_wm_capture_status=pass`,
  `simpleos_host_wm_capture_mode=hosted-wm-capture-stdout-ppm`,
  `simpleos_wm_host_ppm_status=pass`, host scene/window/focus/titlebar/taskbar
  rows pass, and structured compare still blocked on missing RenderDoc log
  comparison / ARGB parity.
- verify: Aggregate follow-up over
  `build\simpleos_multiconfig_live_evidence\wm-host-compare.env` now echoes the
  stdout PPM mode and derives
  `simpleos_wm_structured_compare_evidence_status=blocked:missing-renderdoc-log-compare`
  instead of `blocked:missing-host-wm-scene`. The full lane remains blocked by
  FPGA UART hardware, Engine2D Vulkan, SimpleOS `.rdc`, and WM RenderDoc log
  evidence.
- impl: Hardened the Windows QEMU RV64 build path so `-AttemptBuild` can select
  the nested Simple binary, build backend, and compiler explicitly. The current
  passing path uses `src\compiler_rust\target\debug\simple.exe`,
  `-BuildBackend cranelift`, and
  `-BuildCc C:\dev\install\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin\clang.exe`.
- impl: Added optional `-BuildDiskImage` support to the QEMU and combined
  Windows wrappers. The wrapper compiles `scripts/os/make_os_disk.c` and
  produces `build/os/fat32-riscv64.img`; `scripts/os/make_os_disk.c` now uses
  `_mkdir` on Windows.
- impl: Routed disk-image builder stdout/stderr into
  `build/os/systest/qemu-riscv64-desktop/disk-image-builder-*.log` artifacts
  and exposed those paths through the QEMU wrapper and aggregate checker so
  wrapper stdout remains line-oriented evidence rows.
- impl: Added Windows `.exe` Simple binary candidates to
  `src/os/qemu_runner_part2.spl` so nested QEMU/RV64 build helpers can resolve
  `src/compiler_rust/target/debug/simple.exe`,
  `src/compiler_rust/target/bootstrap/simple.exe`, release, and `bin/*.exe`
  candidates before falling back to extensionless paths.
- impl: Fixed live QEMU serial classification in the Windows wrapper. A guest
  that exits after `SIMPLEOS_RISCV_SMF_FS_PASS` / `TEST PASSED` now records
  `simpleos_qemu_serial_console_status=pass`,
  `simpleos_qemu_rv64_qemu_exit_status=exited:0`, and
  `simpleos_qemu_rv64_live_boot_status=guest-exited-before-service-probes`
  instead of leaving the run as a boot timeout.
- verify: Combined Windows build/image/live command on 2026-06-26:
  `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-multiconfig-live-evidence.ps1 -AttemptBuild -BuildDiskImage -RunLiveBoot -BootTimeoutSeconds 20 -BuildBackend cranelift -BuildCc C:\dev\install\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin\clang.exe`
  recorded `simpleos_qemu_rv64_build_status=pass`,
  `simpleos_qemu_rv64_disk_image_build_status=pass`,
  `simpleos_qemu_rv64_canonical_kernel_status=pass`,
  `simpleos_qemu_rv64_canonical_image_status=pass`,
  `simpleos_qemu_serial_console_status=pass`, and
  `simpleos_qemu_rv64_qemu_exit_status=exited:0`.
- verify: The same combined run still exited nonzero with
  `simpleos_multiconfig_live_status=blocked:qemu-service:blocked:missing-qemu-ssh-banner`.
  Remaining blockers are live SSH/HTTP service probes, QEMU GPU/framebuffer
  readback, structured WM compare, FPGA UART evidence, Engine2D Vulkan
  readback, and SimpleOS RenderDoc `.rdc` evidence.
- runtime-boundary: Reused wrapper/tooling and existing owner modules; no new
  raw `rt_*` extern, alias, or runtime shortcut was added. The edited
  `src/os/qemu_runner_part2.spl` already contains runtime process/env/file
  externs for QEMU orchestration.
- impl: Added `-ProbeHostVulkan` to the Windows Engine2D/RenderDoc normalizer
  and pass-through support in the combined Windows evidence wrapper. The probe
  records host `vulkaninfo --summary`, Vulkan instance/device rows, SDK tool
  visibility, Chrome/Electron presence, RenderDoc tool visibility, and focused
  browser-backing diagnostic rows.
- impl: Extended the aggregate checker to echo the Windows host Vulkan
  readiness and browser-backing rows from merged evidence files.
- docs: Updated the detailed plan, TLDR, UI stack architecture/TLDR,
  GUI/Web/2D Vulkan setup guide, and manual spec mirror with the
  `-ProbeHostVulkan` command and diagnostic-only interpretation.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-multiconfig-live-evidence.ps1 -ProbeHostVulkan` emitted
  `simpleos_windows_vulkaninfo_status=pass`,
  `simpleos_windows_vulkan_instance_version=1.3.301`,
  `simpleos_windows_vulkan_device_name=Intel(R) UHD Graphics 770`,
  `simpleos_windows_vulkan_sdk_tools_status=blocked:sdk-tools-missing`,
  `simpleos_windows_renderdoc_tool_status=missing`, and
  `gui_web_2d_vulkan_browser_backing_status=fail`; the aggregate live status
  remains blocked on missing QEMU/FPGA/Engine2D/RenderDoc/WM evidence.
- impl: Added opt-in `-AttemptBuild` to `scripts/check/check-simpleos-qemu-rv64-desktop-evidence.ps1` and pass-through support in `scripts/check/check-simpleos-multiconfig-live-evidence.ps1`. The preflight runs `src\compiler_rust\target\debug\simple.exe os build --arch=riscv64`, writes `build/os/systest/qemu-riscv64-desktop/rv64-build.log`, refreshes artifact candidate rows, and emits QEMU RV64 build status plus native-build exit rows.
- impl: Extended the aggregate checker to echo QEMU RV64 build attempt rows from merged evidence files, including `simpleos_qemu_rv64_native_build_exit_code`.
- docs: Updated the plan, TLDR, QEMU system-test guide, and manual spec mirror with `-AttemptBuild`, the build log path, and the current Windows native-build crash evidence.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1 -AttemptBuild` emitted `simpleos_qemu_rv64_build_status=blocked:build-exit-1`, `simpleos_qemu_rv64_build_exit_code=1`, `simpleos_qemu_rv64_native_build_exit_code=-1073741819`, and kept the QEMU blocker at `missing-desktop-smf-fs-kernel`.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-multiconfig-live-evidence.ps1 -AttemptBuild` propagated the QEMU build rows through `build/simpleos_multiconfig_live_evidence/simpleos-multiconfig-live.env`; the aggregate status remains `blocked:qemu-service:blocked:missing-qemu-serial-console`.
- impl: Extended `scripts/check/check_simpleos_multiconfig_live_evidence.spl` to echo Windows combined-wrapper diagnostics from merged evidence files, including wrapper name, child wrapper exit codes, aggregate status, and aggregate exit code.
- docs: Updated the detailed plan, TLDR, QEMU guide, and manual spec mirror so operators know the aggregate checker prints the Windows wrapper diagnostics beside the six live evidence gates.
- verify: `SIMPLE_LIB=src src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence build/simpleos_multiconfig_live_evidence/simpleos-multiconfig-live.env --mode=interpreter` printed `simpleos_multiconfig_windows_wrapper=check-simpleos-multiconfig-live-evidence.ps1`, all four child exit codes as `1`, aggregate status `blocked`, aggregate exit code `1`, and the expected blocked live status.
- impl: Added `scripts/check/check-simpleos-multiconfig-live-evidence.ps1`, a Windows combined evidence wrapper that runs the QEMU RV64, FPGA serial, WM host-compare, and Engine2D/RenderDoc wrappers in order, writes `build/simpleos_multiconfig_live_evidence/simpleos-multiconfig-live.env`, and returns the aggregate checker exit code.
- docs: Updated the detailed plan, TLDR, QEMU system-test guide, and manual spec mirror with the combined Windows wrapper command and expected fail-closed current-host result.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-multiconfig-live-evidence.ps1` produced the merged evidence file and exited `1` with `simpleos_multiconfig_live_status=blocked:qemu-service:blocked:missing-qemu-serial-console`; child wrappers each exited `1` because canonical QEMU artifacts, FPGA UART evidence, QEMU/host PPMs, Engine2D Vulkan readback, SimpleOS `.rdc`, and RenderDoc logs are missing.
- impl: Split `scripts/check/check-simpleos-wm-host-compare-evidence.ps1` scene parameters into `-WmSceneName` (`simpleos-desktop-four-windows`) and `-RenderdocSceneName` (`vulkan-engine2d`), and emitted `simpleos_wm_compare_scene` plus `simpleos_wm_renderdoc_scene` diagnostic rows.
- docs: Updated the WM compare guide, detailed plan, TLDR, and manual spec mirror so WM scene identity cannot be confused with the RenderDoc/Engine2D scene name.
- impl: Extended `scripts/check/check-simpleos-engine2d-renderdoc-evidence.ps1` to emit QEMU SimpleOS Engine2D/Vulkan bridge rows and extended `scripts/check/check_simpleos_multiconfig_live_evidence.spl` to print `simpleos_engine2d_vulkan_bridge_status` from raw evidence files.
- verify: `src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence build/simpleos_multiconfig_live_evidence/engine2d-renderdoc.env --mode=interpreter` now derives `simpleos_engine2d_vulkan_bridge_status=blocked:missing-engine2d-vulkan-processing-backend` from the normalizer output while keeping the aggregate live status blocked on missing QEMU service evidence.
- docs: Updated the plan, TLDR, manual spec mirror, and UI stack architecture/TLDR to document the bridge rows and diagnostic aggregate output.
- impl: Added `SimpleOsEngine2dVulkanBridgePlan`, `qemu_riscv64_engine2d_vulkan_bridge_plan()`, and `simpleos_engine2d_vulkan_bridge_required_keys()` to bind QEMU SimpleOS to `virtio_gpu` framebuffer drawing, Vulkan Engine2D processing, `draw_ir-to-engine2d` Simple2D commands, device readback, QMP screendump readback, RenderDoc `capture-simple`, and the shared WM comparison scene.
- impl: Extended `scripts/check/check-simpleos-engine2d-renderdoc-evidence.ps1` to parse QEMU screendump PPM dimensions and emit `simpleos_qemu_gpu_readback_width`, `simpleos_qemu_gpu_readback_height`, and `simpleos_qemu_gpu_readback_dimensions_status`; when Engine2D ARGB metadata is absent, those dimensions fill viewport diagnostics without satisfying the Vulkan backend gate.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-engine2d-renderdoc-evidence.ps1 -ProbeHostVulkan` now records QEMU readback dimensions `320x240`, host Vulkan discovery `pass`, SDK tools `blocked:sdk-tools-missing`, RenderDoc tool `missing`, and still exits nonzero because `simpleos_engine2d_runtime_backend=missing` and SimpleOS `.rdc` magic is absent.
- verify: `SIMPLE_LIB=src src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence build/simpleos_multiconfig_live_evidence/engine2d-renderdoc.env --mode=interpreter` exits `1` with `simpleos_engine2d_vulkan_bridge_status=blocked:missing-engine2d-vulkan-processing-backend`, confirming the new dimensions are diagnostic only.
- verify: Full combined refresh:
  `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-multiconfig-live-evidence.ps1 -BuildDesktopServiceKernel -BuildFpgaSerialKernel -ProbeHostVulkan -BuildBackend cranelift -BuildCc C:\dev\install\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin\clang.exe -RunLiveBoot -BootTimeoutSeconds 45`
  exited `1` as expected, with `simpleos_qemu_service_evidence_status=pass`,
  FPGA serial build rows `pass`, QEMU GPU readback dimensions `320x240`,
  Windows Vulkan discovery `pass`, SDK tools `blocked:sdk-tools-missing`,
  RenderDoc tool `missing`, and aggregate
  `simpleos_multiconfig_live_status=blocked:fpga-serial:blocked:missing-fpga-uart-terminal`.
- impl: Added opt-in `-AttemptHostWmCapture` to `scripts/check/check-simpleos-wm-host-compare-evidence.ps1` and passthrough support in the combined Windows wrapper. The WM wrapper now records hosted-WM capture attempt/mode/status/exit/log rows before validating `host-wm.ppm`; failed or crashed hosted capture remains diagnostic and cannot pass the host-WM gate.
- impl: Extended `scripts/check/check_simpleos_multiconfig_live_evidence.spl` to echo the hosted-WM capture diagnostic rows beside `simpleos_wm_structured_compare_evidence_status`.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-wm-host-compare-evidence.ps1 -BaseEvidencePath build\simpleos_multiconfig_live_evidence\qemu-rv64-desktop.env -AttemptHostWmCapture` records `simpleos_host_wm_capture_status=blocked:host-capture-exit-neg1073741819`, writes `build/simpleos_multiconfig_live_evidence/host-wm-capture.log` with the crashed entrypoint details, records `simpleos_wm_host_ppm_status=missing`, and exits `1` without promoting host WM evidence.
- verify: `SIMPLE_LIB=src src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence build/simpleos_multiconfig_live_evidence/wm-host-compare.env --mode=interpreter` echoes the hosted-WM capture rows and exits `1` with `simpleos_wm_structured_compare_evidence_status=blocked:missing-host-wm-scene`.
- spec: Extended `test/01_unit/os/simpleos_config_matrix_spec.spl` to 14 scenarios, proving the QEMU SimpleOS Engine2D/Vulkan bridge is ready and blocks CPU processing fallback or missing QMP screendump requirements.
- docs: Updated the manual spec mirror, detailed plan, TLDR, and UI stack architecture/TLDR with the SimpleOS Engine2D/Vulkan bridge contract.
- impl: Added `scripts/check/check-simpleos-fpga-rv64-serial-evidence.ps1`, a Windows wrapper that emits FPGA RV64 serial raw rows for board profile, UART terminal, serial device/log boot marker, toolchain, bitstream, and blocked SSH/HTTP/GPU/WM/Vulkan/RenderDoc capability evidence.
- docs: Updated the detailed plan, TLDR, and RISC-V FPGA guide with the FPGA serial wrapper command, environment variable inputs, default evidence path, and fail-closed boot-marker/toolchain/bitstream requirements.
- dev: Created state file with 7 acceptance criteria (type: feature).
- plan: Added `doc/03_plan/os/simpleos_multiconfig_vulkan_wm_plan.md` and TLDR with QEMU RV64, FPGA RV64, Simple2D/Engine2D Vulkan, RenderDoc, and WM comparison tracks plus required evidence keys.
- impl: Added `src/os/simpleos_config_matrix.spl` with explicit `qemu-riscv64-desktop` and `fpga-riscv64-serial` profiles, QEMU SSH/HTTP host ports `2222`/`8080`, QEMU GPU/WM/Vulkan/RenderDoc requirements, and FPGA fail-closed non-serial capability reasons.
- spec: Added `test/01_unit/os/simpleos_config_matrix_spec.spl` to prove QEMU required capabilities are ready at the profile layer, FPGA non-serial capabilities are blocked, and live evidence is still required after the static matrix passes.
- verify: `SIMPLE_LIB=src .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean` passed.
- verify: `Get-ChildItem -Recurse doc\06_spec -Filter *_spec.spl | Measure-Object` reported `0`.
- verify: `.\bin\simple.exe fmt --check src\os\simpleos_config_matrix.spl test\01_unit\os\simpleos_config_matrix_spec.spl` still reports formatting failure while the formatter itself emits existing runtime errors (`repeat`/`extend` missing); files were manually wrapped and the focused test remains green.
- verify: `.\bin\simple.exe check ...` is not usable as focused evidence on this Windows binary because it expanded into the broad cached suite and failed on unrelated existing tests; the focused `simple test` result above is the authoritative check for this slice.
- impl: Extended `src/os/simpleos_config_matrix.spl` with `qemu_riscv64_desktop_qemu_args()`, artifact/kernel/image paths, `qemu_riscv64_desktop_qemu_args_status()`, and `SimpleOsWmRenderdocEvidence` so QEMU RV64 SSH/HTTP/GPU launch intent and WM/RenderDoc completion evidence are machine-checkable before live QEMU runs.
- spec: Rewrote `test/01_unit/os/simpleos_config_matrix_spec.spl` as a real `std.spec` scenario. It now reports 5 counted checks covering QEMU profile capabilities, FPGA serial-only fail-closed behavior, QEMU launch args, WM/RenderDoc evidence keys, and static-matrix/live-evidence separation.
- docs: Updated `doc/03_plan/os/simpleos_multiconfig_vulkan_wm_plan.md`, its TLDR, `doc/07_guide/platform/simpleos/qemu_system_tests.md`, and `doc/07_guide/app/ui/wm_compare.md` with the new QEMU RV64 desktop args and WM/RenderDoc evidence contract.
- docs: Added manual mirrored spec doc `doc/06_spec/test/01_unit/os/simpleos_config_matrix_spec.md`. The available `src\compiler_rust\target\debug\simple.exe spipe-docgen ...` command reports `0/1 complete`, `1/1 stubs`, and runtime errors for missing `trim_end`, so the manual mirror records the current docgen blocker explicitly.
- verify: `SIMPLE_LIB=src .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean` passed with 5 checks; `.\bin\simple.exe test --clean test\01_unit\os\simpleos_config_matrix_spec.spl` also reported the same 5 passing checks from cache.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check` reported `STATUS: PASS spipe-dev-command wiring`.
- verify: `Get-ChildItem -Recurse doc\06_spec -Filter *_spec.spl | Measure-Object` reported `0`.
- verify: `sh scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` could not run because `sh` is unavailable in this Windows environment. No new raw `rt_*` imports or externs were added in this lane.
- impl: Added `SimpleOsQemuServiceEvidence`, `simpleos_qemu_service_required_evidence_keys()`, `simpleos_qemu_service_evidence_status()`, and `passing_simpleos_qemu_service_evidence()` so live QEMU serial, SSH, HTTP, GPU readback, and WM marker checks have a fail-closed contract before wrappers launch QEMU.
- spec: Extended `test/01_unit/os/simpleos_config_matrix_spec.spl` with a sixth scenario proving QEMU service evidence keys are present and that missing SSH banner or missing GPU readback blocks completion.
- docs: Updated the manual spec mirror, QEMU RV64 plan/TLDR, `doc/07_guide/platform/simpleos/qemu_system_tests.md`, and `doc/07_guide/app/ui/wm_compare.md` with the new QEMU service evidence contract.
- verify: `SIMPLE_LIB=src .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter` reported 6 passing scenarios; the runner reused cache on the repeated post-docs run.
- verify: `src\compiler_rust\target\debug\simple.exe spipe-docgen test\01_unit\os\simpleos_config_matrix_spec.spl --output doc\06_spec --no-index` still emitted `0/1 complete`, `1/1 stubs`, and repeated `Function 'trim_end' not found`, so the manual mirror remains the authoritative operator doc for this spec.
- verify: `Get-ChildItem -Recurse doc\06_spec -Filter *_spec.spl | Measure-Object` reported `0`.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check` reported `STATUS: PASS spipe-dev-command wiring`.
- verify: `rg "\brt_[A-Za-z0-9_]+"` over the lane-owned implementation/spec/docs found no raw runtime symbols. `sh` is still unavailable on this Windows host, so `scripts/audit/direct-env-runtime-guard.shs` could not be executed.
- impl: Added QEMU system-test bridge accessors `riscv64_desktop_kernel_path()`, `riscv64_desktop_image_path()`, `riscv64_desktop_qemu_args()`, and `riscv64_desktop_qemu_args_status()` to `src/os/qemu_systest_contract.spl`, delegating to the pure desktop descriptor while leaving the existing serial `riscv64_qemu_args()` unchanged.
- spec/docs: Covered the QEMU system-test desktop bridge in the existing 6-scenario spec and refreshed the manual mirror, plan, and QEMU guide. This bridge added no new `rt_*` calls; the touched system-test contract already had runtime externs for live QEMU execution.
- verify: `SIMPLE_LIB=src .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter` passed after adding the QEMU system-test bridge.
- verify: Final focused pass reported 6 passing scenarios from cache, `doc/06_spec` executable spec count `0`, and `STATUS: PASS spipe-dev-command wiring`. `git diff -U0` for `src/os/qemu_systest_contract.spl` showed only the `os.simpleos_config_matrix` import and pure `riscv64_desktop_*` delegate functions.
- impl: Added `SimpleOsWmStructuredCompareEvidence`, `simpleos_wm_structured_compare_required_evidence_keys()`, `simpleos_wm_structured_compare_status()`, and `passing_simpleos_wm_structured_compare_evidence()` to require QEMU/host scene identity, window counts, focus IDs, titlebar/taskbar status, RenderDoc log comparison, ARGB diff status, and zero ARGB mismatches before a WM comparison can pass.
- spec: Extended the focused spec to 7 scenarios, proving structured WM comparison passes only with complete metadata and blocks scene mismatch, missing RenderDoc log comparison, and nonzero ARGB mismatches.
- docs: Updated the manual spec mirror, plan, TLDR, and WM compare guide with the structured QEMU-vs-host WM comparison evidence rows.
- verify: `SIMPLE_LIB=src .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter` reported 7 passing scenarios; the repeated verification run reused cache.
- verify: `Get-ChildItem -Recurse doc\06_spec -Filter *_spec.spl | Measure-Object` reported `0`.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check` reported `STATUS: PASS spipe-dev-command wiring`.
- verify: `rg "\brt_[A-Za-z0-9_]+"` over the lane-owned pure implementation/spec/docs found no raw runtime symbols.
- verify: `src\compiler_rust\target\debug\simple.exe spipe-docgen test\01_unit\os\simpleos_config_matrix_spec.spl --output doc\06_spec --no-index` still emitted `0/1 complete`, `1/1 stubs`, and repeated `Function 'trim_end' not found`; the manual mirror remains authoritative.
- verify: `Get-Command sh` reported unavailable, so `scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` still could not run in this Windows PowerShell environment.
- impl: Added `examples/09_embedded/simple_os/arch/riscv64/desktop_service_entry.spl` and `examples/09_embedded/simple_os/arch/riscv64/boot/full_networking_runtime.c` aliases for the QEMU RV64 desktop-service artifact. The entry runs the SMF-FS smoke markers, initializes the noalloc PMM, brings up PCI virtio-net, serves SSH banner and HTTP, initializes PCI virtio-gpu, and emits display/WM markers.
- impl: Replaced the stale absolute include in `full_networking_runtime.c` with a repo-relative include of `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`, guarded the freestanding `_start` shim behind `SIMPLE_FREESTANDING_RUNTIME_NO_ENTRY`, and raised the PCI net queue cap to accept QEMU's 256-entry legacy queue.
- runtime-boundary: runtime_need = freestanding QEMU RV64 desktop service probes for PCI net, boot TCP, PCI display, QMP-readback, and SMF-FS smoke in one current-source boot artifact. facade_checked = existing smoke entry, MMIO `baremetal_stubs.c`, HTTP/TCP baremetal path, and freestanding runtime owner path. chosen_path = build-local owner alias over the existing freestanding runtime bridge (`rt_desktop_pci_*`) plus explicit PMM init; rejected_shortcuts = no fake SSH/HTTP rows, no host-only shim, no screenshot-only pass, no app-level raw runtime expansion outside the freestanding boot owner.
- impl: Updated `scripts/check/check-simpleos-qemu-rv64-desktop-evidence.ps1` with shared serial-log reads, PCI net/GPU QEMU args, monotonic SSH/HTTP/GPU rows, passing blocker row, and `-BuildDesktopServiceKernel` rows. Updated the combined Windows wrapper to forward `-BuildDesktopServiceKernel`.
- impl: Updated the static config matrix, tests, Engine2D wrapper, and aggregate checker to use `virtio-net-pci,netdev=rvnet` and `virtio-gpu-pci,disable-modern=on,disable-legacy=off` for the QEMU desktop path.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1 -BuildDesktopServiceKernel -BuildBackend cranelift -BuildCc C:\dev\install\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin\clang.exe -RunLiveBoot -BootTimeoutSeconds 45` exited `0` with serial, SSH banner `SSH-2.0-SimpleOS_1.0`, HTTP `200`, QMP screendump pass/nonblank pass, GPU readback pass, WM marker pass, and `simpleos_qemu_rv64_blocker=pass`.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-multiconfig-live-evidence.ps1 -BuildDesktopServiceKernel -BuildBackend cranelift -BuildCc C:\dev\install\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin\clang.exe -RunLiveBoot -BootTimeoutSeconds 45` exited `1` as expected with QEMU child exit `0`, `simpleos_qemu_service_evidence_status=pass`, and aggregate status `blocked:fpga-serial:blocked:missing-fpga-uart-terminal`; Engine2D Vulkan, RenderDoc, host-WM, and structured compare remain incomplete.
- impl: Added `examples/09_embedded/simple_os/arch/riscv64/fpga_serial_entry.spl`, a serial-only FPGA boot entry that emits `SIMPLEOS_FPGA_RISCV64_SERIAL_BOOT`, `TEST PASSED`, and explicit blocked SSH/HTTP/GPU/WM/Vulkan/RenderDoc markers.
- impl: Added FPGA serial entry/kernel/marker accessors to `src/os/simpleos_config_matrix.spl`, extended the focused spec/manual with those requirements, and extended `simpleos_fpga_serial_required_evidence_keys()` with expected entry/kernel rows.
- impl: Added `-BuildFpgaSerialKernel` to `scripts/check/check-simpleos-fpga-rv64-serial-evidence.ps1` and passthrough support in the combined Windows wrapper. The FPGA wrapper now emits expected entry/kernel/build rows and marker diagnostics (`rv64 boot` and `TEST PASSED`) while still requiring the canonical FPGA boot marker for pass.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-fpga-rv64-serial-evidence.ps1 -BuildFpgaSerialKernel -BuildBackend cranelift -BuildCc C:\dev\install\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin\clang.exe` built `build/os/simpleos_riscv64_fpga.elf` and emitted `simpleos_fpga_build_status=pass`; it still exited `1` because no real serial device/log/toolchain/bitstream evidence was supplied.
- verify: Synthetic parser smoke with a temporary serial log containing `SIMPLEOS_FPGA_RISCV64_SERIAL_BOOT`, serial device `uart0`, toolchain status `pass`, and bitstream status `pass` exited `0`, proving the wrapper pass path without claiming hardware evidence.
- impl: Added `-RunLiveBoot` mode to `scripts/check/check-simpleos-qemu-rv64-desktop-evidence.ps1`. The live path launches QEMU only after canonical `build/os/simpleos_riscv64_smf_fs.elf` and `build/os/fat32-riscv64.img` exist, captures serial output under `build/os/systest/qemu-riscv64-desktop/serial.log`, waits for RV64 FS-exec or network/http serial markers, probes SSH `2222` and HTTP `8080`, and still blocks GPU/WM rows until real readback and structured WM evidence exist.
- docs: Updated the detailed plan, TLDR, and QEMU system-test guide with the live QEMU wrapper command, emitted live-mode rows, and the rule that `Display service ready` or WM serial markers are diagnostic unless paired with GPU readback/structured WM evidence.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1` still found `qemu-system-riscv64.exe`, reported candidate statuses `none`, emitted `simpleos_qemu_rv64_live_boot_requested=false`, and exited `1` with `simpleos_qemu_rv64_blocker=missing-desktop-smf-fs-kernel`.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1 -RunLiveBoot` emitted `simpleos_qemu_rv64_live_boot_requested=true`, `simpleos_qemu_rv64_live_boot_status=blocked:missing-desktop-smf-fs-kernel`, `simpleos_qemu_rv64_qemu_exit_status=not-started`, and exited `1` without launching QEMU because canonical artifacts are missing.
- verify: `SIMPLE_LIB=src src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence build/simpleos_multiconfig_live_evidence/qemu-rv64-desktop.env --mode=interpreter` consumed the live-mode wrapper output and still exited `1` with `simpleos_multiconfig_live_status=blocked:qemu-service:blocked:missing-qemu-serial-console`.
- verify: Final live-wrapper pass on 2026-06-26: `SIMPLE_LIB=src .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean` reported 13 passing scenarios.
- verify: Final live-wrapper pass on 2026-06-26: `Get-ChildItem -Recurse doc\06_spec -Filter *_spec.spl | Measure-Object` reported `0`.
- verify: Final live-wrapper pass on 2026-06-26: `powershell -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check` reported `STATUS: PASS spipe-dev-command wiring`.
- verify: Final live-wrapper pass on 2026-06-26: `Select-String -Pattern '\brt_[A-Za-z0-9_]+'` over the lane-owned implementation/spec/checker/docs returned no raw runtime symbols.
- verify: Final live-wrapper pass on 2026-06-26: `src\compiler_rust\target\debug\simple.exe spipe-docgen test\01_unit\os\simpleos_config_matrix_spec.spl --output doc\06_spec --no-index` still emitted `0/1 complete`, `1/1 stubs`, and repeated `Function 'trim_end' not found`; the manual mirror remains authoritative.
- verify: Final live-wrapper pass on 2026-06-26: `Get-Command sh` reported unavailable, so Unix-only `scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` remain blocked in this Windows PowerShell environment.
- impl: Extended the QEMU RV64 desktop live wrapper with QMP `screendump` support. Live mode now exposes `127.0.0.1:4444`, emits QMP/screendump artifact rows, captures `build/os/systest/qemu-riscv64-desktop/qemu-screendump.ppm` after `Display service ready`, validates P6/nonblank bytes, and only then allows `simpleos_qemu_gpu_readback_status=pass`.
- docs: Updated the QEMU system-test guide, detailed plan, and TLDR so operators know QEMU GPU proof comes from nonblank QMP PPM readback, while structured WM compare and RenderDoc remain separate gates.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1` emitted the new QMP rows with `simpleos_qemu_rv64_qmp_status=not-requested`, `simpleos_qemu_rv64_screendump_status=not-requested`, and remained fail-closed with `simpleos_qemu_rv64_blocker=missing-desktop-smf-fs-kernel`.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1 -RunLiveBoot` emitted the new QMP rows with `simpleos_qemu_rv64_live_boot_status=blocked:missing-desktop-smf-fs-kernel`, `simpleos_qemu_rv64_qmp_status=not-requested`, and did not launch QEMU because canonical artifacts are still missing.
- verify: Final QMP-readback wrapper pass on 2026-06-26: `SIMPLE_LIB=src src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence build/simpleos_multiconfig_live_evidence/qemu-rv64-desktop.env --mode=interpreter` consumed the wrapper output and exited `1` with `simpleos_multiconfig_live_status=blocked:qemu-service:blocked:missing-qemu-serial-console`.
- verify: Final QMP-readback wrapper pass on 2026-06-26: `SIMPLE_LIB=src .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean` reported 13 passing scenarios.
- verify: Final QMP-readback wrapper pass on 2026-06-26: `Get-ChildItem -Recurse doc\06_spec -Filter *_spec.spl | Measure-Object` reported `0`.
- verify: Final QMP-readback wrapper pass on 2026-06-26: `powershell -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check` reported `STATUS: PASS spipe-dev-command wiring`.
- verify: Final QMP-readback wrapper pass on 2026-06-26: `Select-String -Pattern '\brt_[A-Za-z0-9_]+'` over the lane-owned implementation/spec/checker/docs returned no raw runtime symbols.
- verify: Final QMP-readback wrapper pass on 2026-06-26: `src\compiler_rust\target\debug\simple.exe spipe-docgen test\01_unit\os\simpleos_config_matrix_spec.spl --output doc\06_spec --no-index` still emitted `0/1 complete`, `1/1 stubs`, and repeated `Function 'trim_end' not found`; the manual mirror remains authoritative.
- verify: Final QMP-readback wrapper pass on 2026-06-26: `Get-Command sh` reported unavailable, so Unix-only `scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` remain blocked in this Windows PowerShell environment.
- impl: Added `scripts/check/check-simpleos-wm-host-compare-evidence.ps1`, a Windows wrapper that merges base QEMU evidence with host/QEMU WM comparison rows, validates QEMU and host PPM captures, exact byte mismatch count, RenderDoc `.rdc` magic/size, capture log status, and QEMU/host WM RenderDoc log paths.
- docs: Updated the WM compare guide, detailed plan, and TLDR with the host/QEMU WM wrapper command, default artifact paths, and aggregate checker handoff.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-wm-host-compare-evidence.ps1 -BaseEvidencePath build/simpleos_multiconfig_live_evidence/qemu-rv64-desktop.env` emitted missing QEMU/host PPM statuses, `simpleos_wm_argb_mismatch_count=-1`, missing RenderDoc `.rdc` magic/log rows, and exited `1`.
- verify: `SIMPLE_LIB=src src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence build/simpleos_multiconfig_live_evidence/wm-host-compare.env --mode=interpreter` consumed the merged WM evidence and exited `1` with QEMU service blocked at `missing-qemu-serial-console`, RenderDoc artifact blocked at `missing-simple-rdoc-magic`, structured WM blocked at `missing-qemu-wm-scene`, and WM RenderDoc blocked at `missing-simple-rdoc-magic`.
- verify: Final WM-host-wrapper pass on 2026-06-26: `SIMPLE_LIB=src .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean` reported 13 passing scenarios.
- verify: Final WM-host-wrapper pass on 2026-06-26: `Get-ChildItem -Recurse doc\06_spec -Filter *_spec.spl | Measure-Object` reported `0`.
- verify: Final WM-host-wrapper pass on 2026-06-26: `powershell -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check` reported `STATUS: PASS spipe-dev-command wiring`.
- verify: Final WM-host-wrapper pass on 2026-06-26: `Select-String -Pattern '\brt_[A-Za-z0-9_]+'` over the lane-owned implementation/spec/checker/docs returned no raw runtime symbols.
- verify: Final WM-host-wrapper pass on 2026-06-26: `src\compiler_rust\target\debug\simple.exe spipe-docgen test\01_unit\os\simpleos_config_matrix_spec.spl --output doc\06_spec --no-index` still emitted `0/1 complete`, `1/1 stubs`, and repeated `Function 'trim_end' not found`; the manual mirror remains authoritative.
- verify: Final WM-host-wrapper pass on 2026-06-26: `Get-Command sh` reported unavailable, so Unix-only `scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` remain blocked in this Windows PowerShell environment.
- impl: Added `scripts/check/check-simpleos-engine2d-renderdoc-evidence.ps1`, a Windows normalizer that merges prior evidence with Engine2D Vulkan backend/readback rows and SimpleOS RenderDoc artifact rows. It reads `build/gui-web-2d-vulkan-env/evidence.env` when present, validates QEMU screendump readback, SimpleOS `.rdc` magic/size, capture logs, and QEMU/host WM RenderDoc logs.
- docs: Updated the detailed plan, TLDR, and UI stack architecture/TLDR with the Engine2D/RenderDoc normalizer command and artifact role.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-engine2d-renderdoc-evidence.ps1 -BaseEvidencePath build/simpleos_multiconfig_live_evidence/wm-host-compare.env` emitted missing Engine2D backend/readback rows, missing QEMU GPU readback, missing SimpleOS `.rdc` magic/log rows, and exited `1`.
- verify: `SIMPLE_LIB=src src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence build/simpleos_multiconfig_live_evidence/engine2d-renderdoc.env --mode=interpreter` consumed the normalized evidence and exited `1` with QEMU service blocked at `missing-qemu-serial-console`, Engine2D Vulkan blocked at `missing-engine2d-vulkan-backend`, RenderDoc artifact blocked at `missing-simple-rdoc-magic`, structured WM blocked at `missing-qemu-wm-scene`, and WM RenderDoc blocked at `missing-simple-rdoc-magic`.
- verify: Final Engine2D/RenderDoc wrapper pass on 2026-06-26: `SIMPLE_LIB=src .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean` reported 13 passing scenarios.
- verify: Final Engine2D/RenderDoc wrapper pass on 2026-06-26: `Get-ChildItem -Recurse doc\06_spec -Filter *_spec.spl | Measure-Object` reported `0`.
- verify: Final Engine2D/RenderDoc wrapper pass on 2026-06-26: `powershell -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check` reported `STATUS: PASS spipe-dev-command wiring`.
- verify: Final Engine2D/RenderDoc wrapper pass on 2026-06-26: `Select-String -Pattern '\brt_[A-Za-z0-9_]+'` over the lane-owned implementation/spec/checker/docs returned no raw runtime symbols.
- verify: Final Engine2D/RenderDoc wrapper pass on 2026-06-26: `src\compiler_rust\target\debug\simple.exe spipe-docgen test\01_unit\os\simpleos_config_matrix_spec.spl --output doc\06_spec --no-index` still emitted `0/1 complete`, `1/1 stubs`, and repeated `Function 'trim_end' not found`; the manual mirror remains authoritative.
- verify: Final Engine2D/RenderDoc wrapper pass on 2026-06-26: `Get-Command sh` reported unavailable, so Unix-only `scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` remain blocked in this Windows PowerShell environment.
- verify: Final wrapper-diagnostic pass on 2026-06-26: `SIMPLE_LIB=src .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean` reported 13 passing scenarios.
- verify: Final wrapper-diagnostic pass on 2026-06-26: `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1` found `C:\dev\tool\msys2\mingw64\bin\qemu-system-riscv64.exe`, emitted canonical/legacy/FPGA/storage candidate diagnostics, reported candidate statuses `none`, and exited `1` with `simpleos_qemu_rv64_blocker=missing-desktop-smf-fs-kernel`.
- verify: Final wrapper-diagnostic pass on 2026-06-26: `SIMPLE_LIB=src src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence build/simpleos_multiconfig_live_evidence/qemu-rv64-desktop.env --mode=interpreter` consumed the wrapper output and exited `1` with `simpleos_multiconfig_live_status=blocked:qemu-service:blocked:missing-qemu-serial-console`.
- verify: Final wrapper-diagnostic pass on 2026-06-26: `Get-ChildItem -Recurse doc\06_spec -Filter *_spec.spl | Measure-Object` reported `0`.
- verify: Final wrapper-diagnostic pass on 2026-06-26: `powershell -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check` reported `STATUS: PASS spipe-dev-command wiring`.
- verify: Final wrapper-diagnostic pass on 2026-06-26: `Select-String -Pattern '\brt_[A-Za-z0-9_]+'` over the lane-owned implementation/spec/checker/docs returned no raw runtime symbols.
- verify: Final wrapper-diagnostic pass on 2026-06-26: `src\compiler_rust\target\debug\simple.exe spipe-docgen test\01_unit\os\simpleos_config_matrix_spec.spl --output doc\06_spec --no-index` still emitted `0/1 complete`, `1/1 stubs`, and repeated `Function 'trim_end' not found`; the manual mirror remains authoritative.
- verify: Final wrapper-diagnostic pass on 2026-06-26: `Get-Command sh` reported unavailable, so Unix-only `scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` remain blocked in this Windows PowerShell environment.
- impl: Extended `scripts/check/check-simpleos-qemu-rv64-desktop-evidence.ps1` with canonical desktop, legacy smoke, FPGA, and storage-probe artifact diagnostics while keeping the QEMU desktop service rows fail-closed until canonical SMF-FS/FAT32 artifacts and live serial/SSH/HTTP/GPU/WM probes pass.
- docs: Updated the detailed plan, TLDR, and QEMU system-test guide to document the new QEMU artifact-diagnostic rows and the rule that legacy/FPGA candidates are diagnostics only.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1` found `C:\dev\tool\msys2\mingw64\bin\qemu-system-riscv64.exe`, reported no canonical, legacy, FPGA, storage-probe, or FAT32 artifact candidates, wrote `build/simpleos_multiconfig_live_evidence/qemu-rv64-desktop.env`, and exited `1` with `simpleos_qemu_rv64_blocker=missing-desktop-smf-fs-kernel`.
- verify: `SIMPLE_LIB=src src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence build/simpleos_multiconfig_live_evidence/qemu-rv64-desktop.env --mode=interpreter` consumed the updated wrapper output and still exited `1` with `simpleos_multiconfig_live_status=blocked:qemu-service:blocked:missing-qemu-serial-console`.
- verify: Final aggregate-gate pass on 2026-06-26: `SIMPLE_LIB=src .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter` reported 11 passing scenarios.
- verify: Final aggregate-gate pass on 2026-06-26: `Get-ChildItem -Recurse doc\06_spec -Filter *_spec.spl | Measure-Object` reported `0`.
- verify: Final aggregate-gate pass on 2026-06-26: `powershell -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check` reported `STATUS: PASS spipe-dev-command wiring`.
- verify: Final aggregate-gate pass on 2026-06-26: `Select-String -Pattern '\brt_[A-Za-z0-9_]+'` over the lane-owned pure implementation/spec/docs returned no raw runtime symbols.
- verify: Final aggregate-gate pass on 2026-06-26: `src\compiler_rust\target\debug\simple.exe spipe-docgen test\01_unit\os\simpleos_config_matrix_spec.spl --output doc\06_spec --no-index` still emitted `0/1 complete`, `1/1 stubs`, and repeated `Function 'trim_end' not found`; the manual mirror remains authoritative.
- verify: Final aggregate-gate pass on 2026-06-26: `Get-Command sh` reported unavailable, so Unix-only `scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` remain blocked in this Windows PowerShell environment.
- impl: Added explicit missing-evidence constructors and `default_blocked_simpleos_multiconfig_live_evidence()` so the aggregate gate has a first-class no-artifact state instead of relying on ad hoc placeholder strings.
- impl: Added `scripts/check/check_simpleos_multiconfig_live_evidence.spl`, a runnable aggregate status emitter that prints QEMU RV64 profile/ports, FPGA serial profile, required aggregate evidence keys, each per-lane status row, and `simpleos_multiconfig_live_status`.
- spec: Extended the focused spec to 12 scenarios, proving default live evidence remains blocked with QEMU service, FPGA serial, Engine2D Vulkan, RenderDoc artifact, structured WM compare, and WM RenderDoc reasons.
- docs: Updated the plan, TLDR, manual spec mirror, QEMU system-test guide, and WM compare guide to name `scripts/check/check_simpleos_multiconfig_live_evidence.spl` as the canonical aggregate status emitter.
- verify: `SIMPLE_LIB=src .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean` reported 12 passing scenarios.
- verify: `SIMPLE_LIB=src src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --mode=interpreter` printed `simpleos_multiconfig_live_status=blocked:qemu-service:blocked:missing-qemu-serial-console` and exited `1`, which is the expected no-artifact result.
- verify: Direct source execution through `.\bin\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --mode=interpreter` is not usable in this Windows shell because this binary reports `file not found` for direct `.spl` paths, matching existing script-path behavior. The Rust debug binary executed the checker.
- verify: `Get-ChildItem -Recurse doc\06_spec -Filter *_spec.spl | Measure-Object` reported `0`.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check` reported `STATUS: PASS spipe-dev-command wiring`.
- verify: `Select-String -Pattern '\brt_[A-Za-z0-9_]+'` over the lane-owned pure implementation/spec/checker/docs returned no raw runtime symbols.
- verify: `src\compiler_rust\target\debug\simple.exe spipe-docgen test\01_unit\os\simpleos_config_matrix_spec.spl --output doc\06_spec --no-index` still emitted `0/1 complete`, `1/1 stubs`, and repeated `Function 'trim_end' not found`; the manual mirror remains authoritative.
- verify: `Get-Command sh` reported unavailable, so Unix-only `scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` remain blocked in this Windows PowerShell environment.
- impl: Added `scripts/check/check-simpleos-qemu-rv64-desktop-evidence.ps1`, a Windows-runnable QEMU RV64 desktop preflight wrapper that writes raw QEMU service evidence rows to `build/simpleos_multiconfig_live_evidence/qemu-rv64-desktop.env`.
- docs: Updated the detailed plan, TLDR, and QEMU system-test guide with the PowerShell QEMU RV64 evidence wrapper command and aggregate checker handoff.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1` found `C:\dev\tool\msys2\mingw64\bin\qemu-system-riscv64.exe`, wrote the QEMU evidence file, and exited `1` because `build/os/simpleos_riscv64_smf_fs.elf` and `build/os/fat32-riscv64.img` are missing.
- verify: `SIMPLE_LIB=src src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence build/simpleos_multiconfig_live_evidence/qemu-rv64-desktop.env --mode=interpreter` consumed the wrapper output and exited `1` with `simpleos_multiconfig_live_status=blocked:qemu-service:blocked:missing-qemu-serial-console`.
- verify: `SIMPLE_LIB=src .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean` reported 13 passing scenarios.
- verify: `Get-ChildItem -Recurse doc\06_spec -Filter *_spec.spl | Measure-Object` reported `0`.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check` reported `STATUS: PASS spipe-dev-command wiring`.
- verify: `Select-String -Pattern '\brt_[A-Za-z0-9_]+'` over the lane-owned implementation/spec/checker/docs returned no raw runtime symbols.
- verify: `src\compiler_rust\target\debug\simple.exe spipe-docgen test\01_unit\os\simpleos_config_matrix_spec.spl --output doc\06_spec --no-index` still emitted `0/1 complete`, `1/1 stubs`, and repeated `Function 'trim_end' not found`; the manual mirror remains authoritative.
- verify: `Get-Command sh` reported unavailable, so Unix-only `scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` remain blocked in this Windows PowerShell environment.
- impl: Extended `scripts/check/check_simpleos_multiconfig_live_evidence.spl` so `--evidence <path>` files may contain either the six aggregate status rows or the raw per-lane QEMU, FPGA, Engine2D Vulkan, RenderDoc artifact, structured WM compare, and WM RenderDoc evidence keys. Missing raw rows still derive blocked statuses.
- docs: Updated the detailed plan, TLDR, manual spec mirror, QEMU system-test guide, and WM compare guide to document raw-row ingestion in addition to aggregate six-row handoff.
- verify: `SIMPLE_LIB=src .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean` reported 13 passing scenarios.
- verify: `SIMPLE_LIB=src src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --mode=interpreter` printed default blocked rows and exited `1`.
- verify: `SIMPLE_LIB=src src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence build/simpleos_multiconfig_live_evidence/passing.env --mode=interpreter` consumed the six aggregate status rows and exited `0` with `simpleos_multiconfig_live_status=pass`.
- verify: `SIMPLE_LIB=src src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence build/simpleos_multiconfig_live_evidence/raw-passing.env --mode=interpreter` consumed detailed raw rows for every lane and exited `0` with all six derived status rows set to `pass`.
- verify: `Get-ChildItem -Recurse doc\06_spec -Filter *_spec.spl | Measure-Object` reported `0`.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check` reported `STATUS: PASS spipe-dev-command wiring`.
- verify: `Select-String -Pattern '\brt_[A-Za-z0-9_]+'` over the lane-owned pure implementation/spec/checker/docs returned no raw runtime symbols; checker I/O remains routed through `std.nogc_sync_mut.io_runtime`.
- verify: `src\compiler_rust\target\debug\simple.exe spipe-docgen test\01_unit\os\simpleos_config_matrix_spec.spl --output doc\06_spec --no-index` still emitted `0/1 complete`, `1/1 stubs`, and repeated `Function 'trim_end' not found`; the manual mirror remains authoritative.
- verify: `Get-Command sh` reported unavailable, so Unix-only `scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` remain blocked in this Windows PowerShell environment.
- impl: Added `simpleos_multiconfig_live_evidence_from_status_rows()` so QEMU/FPGA/Engine2D/RenderDoc/WM live wrappers can hand off the six aggregate lane statuses without duplicating aggregation logic.
- impl: Extended `scripts/check/check_simpleos_multiconfig_live_evidence.spl` to accept `--evidence <path>` or `SIMPLEOS_MULTICONFIG_EVIDENCE`, parse line-oriented `key=value` rows, preserve fail-closed defaults for missing rows, and exit `0` only when `simpleos_multiconfig_live_status=pass`.
- spec: Extended the focused spec to 13 scenarios, proving six passing status rows aggregate to `pass`, a blocked QEMU row identifies the QEMU service lane, and a blocked WM structured-compare row identifies the WM comparison lane.
- docs: Updated the plan, TLDR, manual spec mirror, QEMU system-test guide, and WM compare guide with the aggregate checker evidence-file handoff format.
- verify: `SIMPLE_LIB=src .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter --clean` reported 13 passing scenarios.
- verify: `SIMPLE_LIB=src src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --mode=interpreter` printed default blocked rows and exited `1` with `simpleos_multiconfig_live_status=blocked:qemu-service:blocked:missing-qemu-serial-console`.
- verify: A generated `build/simpleos_multiconfig_live_evidence/passing.env` containing all six `simpleos_*_evidence_status=pass` rows made `SIMPLE_LIB=src src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence build/simpleos_multiconfig_live_evidence/passing.env --mode=interpreter` print `simpleos_multiconfig_live_status=pass` and exit `0`.
- verify: `Get-ChildItem -Recurse doc\06_spec -Filter *_spec.spl | Measure-Object` reported `0`.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check` reported `STATUS: PASS spipe-dev-command wiring`.
- verify: `Select-String -Pattern '\brt_[A-Za-z0-9_]+'` over the lane-owned pure implementation/spec/checker/docs returned no raw runtime symbols; the checker uses `std.nogc_sync_mut.io_runtime` facades for env, args, and file reads.
- verify: `src\compiler_rust\target\debug\simple.exe spipe-docgen test\01_unit\os\simpleos_config_matrix_spec.spl --output doc\06_spec --no-index` still emitted `0/1 complete`, `1/1 stubs`, and repeated `Function 'trim_end' not found`; the manual mirror remains authoritative.
- verify: `Get-Command sh` reported unavailable, so Unix-only `scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` remain blocked in this Windows PowerShell environment.
- impl: Added `SimpleOsMulticonfigLiveEvidence`, `simpleos_multiconfig_live_required_evidence_keys()`, `simpleos_multiconfig_live_status()`, and `passing_simpleos_multiconfig_live_evidence()` as the aggregate fail-closed gate over QEMU service, FPGA serial, Engine2D Vulkan, RenderDoc artifact, structured WM compare, and WM RenderDoc statuses.
- spec: Extended the focused spec to 11 scenarios, proving the aggregate gate passes only when every underlying lane status passes and identifies blocked QEMU service, FPGA serial, and RenderDoc artifact lanes.
- docs: Updated the manual spec mirror, plan, TLDR, WM compare guide, and QEMU system-test guide with the aggregate live evidence gate.
- impl: Added `SimpleOsFpgaSerialEvidence`, `simpleos_fpga_serial_required_evidence_keys()`, `simpleos_fpga_serial_status()`, and `passing_simpleos_fpga_serial_evidence()` to require the `fpga-riscv64-serial` profile, UART terminal status, serial device, serial boot marker, toolchain status, bitstream status, and blocked SSH/HTTP/GPU/WM/Vulkan/RenderDoc statuses.
- spec: Extended the focused spec to 10 scenarios, proving FPGA serial evidence passes only with UART/boot/toolchain/bitstream evidence and blocks missing UART, mistakenly enabled SSH, and mistakenly enabled GPU.
- docs: Updated the manual spec mirror, plan, TLDR, QEMU system-test guide, and RISC-V FPGA guide with the FPGA serial evidence contract and fail-closed desktop capability rule.
- verify: `SIMPLE_LIB=src .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter` reported 10 passing scenarios; the repeated verification run reused cache.
- verify: `Get-ChildItem -Recurse doc\06_spec -Filter *_spec.spl | Measure-Object` reported `0`.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check` reported `STATUS: PASS spipe-dev-command wiring`.
- verify: `Select-String -Pattern '\brt_[A-Za-z0-9_]+'` over the lane-owned pure implementation/spec/docs returned no raw runtime symbols.
- verify: `src\compiler_rust\target\debug\simple.exe spipe-docgen test\01_unit\os\simpleos_config_matrix_spec.spl --output doc\06_spec --no-index` still emitted `0/1 complete`, `1/1 stubs`, and repeated `Function 'trim_end' not found`; the manual mirror remains authoritative.
- verify: `Get-Command sh` reported unavailable, so `scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` still could not run in this Windows PowerShell environment.
- impl: Added `SimpleOsRenderdocArtifactEvidence`, `simpleos_renderdoc_artifact_required_evidence_keys()`, `simpleos_renderdoc_artifact_status()`, and `passing_simpleos_renderdoc_artifact_evidence()` to require `capture-simple`, a SimpleOS `.rdc` path, `RDOC` magic, payload bytes, capture log path/status, Vulkan Engine2D metadata, RenderDoc helper pass status, and QEMU/host WM RenderDoc log paths.
- spec: Extended the focused spec to 9 scenarios, proving the RenderDoc artifact contract blocks `capture-html`, missing `RDOC` magic, header-only `.rdc` payloads, and missing host WM RenderDoc logs.
- docs: Updated the manual spec mirror, plan, TLDR, and WM compare guide with the RenderDoc artifact contract and the distinction between artifact validation and visual/structured comparison.
- verify: `SIMPLE_LIB=src .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter` reported 9 passing scenarios; the repeated verification run reused cache.
- verify: `Get-ChildItem -Recurse doc\06_spec -Filter *_spec.spl | Measure-Object` reported `0`.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check` reported `STATUS: PASS spipe-dev-command wiring`; the command also printed the existing `.gitconfig` warning.
- verify: `Select-String -Pattern '\brt_[A-Za-z0-9_]+'` over the lane-owned pure implementation/spec/docs returned no raw runtime symbols; the shell still printed the existing `.gitconfig` warning.
- verify: `src\compiler_rust\target\debug\simple.exe spipe-docgen test\01_unit\os\simpleos_config_matrix_spec.spl --output doc\06_spec --no-index` still emitted `0/1 complete`, `1/1 stubs`, and repeated `Function 'trim_end' not found`; the manual mirror remains authoritative.
- verify: `Get-Command sh` reported unavailable, so `scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` still could not run in this Windows PowerShell environment.
- impl: Added `SimpleOsEngine2dVulkanEvidence`, `simpleos_engine2d_vulkan_required_evidence_keys()`, `simpleos_engine2d_vulkan_status()`, and `passing_simpleos_engine2d_vulkan_evidence()` to require Vulkan backend, `vulkan-engine2d` scene, Simple2D command status, Vulkan device name, viewport dimensions, readback checksum, nonblank readback, and QEMU GPU readback before the Simple2D/Engine2D path can pass.
- spec: Extended the focused spec to 8 scenarios, proving Engine2D Vulkan evidence blocks CPU fallback, missing readback checksum, and missing QEMU GPU readback.
- docs: Updated the manual spec mirror, plan, TLDR, and UI stack architecture/TLDR with the SimpleOS RV64 Engine2D/Vulkan readback evidence contract.
- verify: `SIMPLE_LIB=src .\bin\simple.exe test test\01_unit\os\simpleos_config_matrix_spec.spl --mode=interpreter` reported 8 passing scenarios; the repeated verification run reused cache.
- verify: `Get-ChildItem -Recurse doc\06_spec -Filter *_spec.spl | Measure-Object` reported `0`.
- verify: `powershell -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check` reported `STATUS: PASS spipe-dev-command wiring`.
- verify: `rg "\brt_[A-Za-z0-9_]+"` over the lane-owned pure implementation/spec/docs found no raw runtime symbols.
- verify: `src\compiler_rust\target\debug\simple.exe spipe-docgen test\01_unit\os\simpleos_config_matrix_spec.spl --output doc\06_spec --no-index` still emitted `0/1 complete`, `1/1 stubs`, and repeated `Function 'trim_end' not found`; the manual mirror remains authoritative.
- verify: `Get-Command sh` reported unavailable, so `scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` still could not run in this Windows PowerShell environment.
