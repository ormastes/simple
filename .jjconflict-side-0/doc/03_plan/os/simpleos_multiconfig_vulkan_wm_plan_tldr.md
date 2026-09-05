# SimpleOS Multi-Config Vulkan WM TLDR

Goal: one fail-closed contract for QEMU RV64 desktop and FPGA RV64 serial, then build Vulkan/RenderDoc WM comparison on top.

```sdn
flow |from, to, gate|
    "profile", "qemu-riscv64-desktop", "ssh+http+gpu+wm+vulkan+renderdoc"
    "profile", "fpga-riscv64-serial", "uart-only"
    "engine2d", "vulkan", "readback+backend+rdc"
    "wm", "host-compare", "structured-state+pixels"
```

Current slice:
- Adds `src/os/simpleos_config_matrix.spl`.
- Adds `test/01_unit/os/simpleos_config_matrix_spec.spl`.
- Documents the detailed implementation/evidence plan.
- Publishes QEMU RV64 desktop args with SSH `2222`, HTTP `8080`,
  `virtio-net-pci`, `virtio-gpu-pci,disable-modern=on,disable-legacy=off`,
  headless QMP screendump, and serial log evidence.
- Publishes FPGA RV64 serial evidence keys for the buildable serial entry,
  expected FPGA ELF, UART terminal, serial device, boot marker, toolchain,
  bitstream, and blocked SSH/HTTP/GPU/WM/Vulkan/RenderDoc statuses.
- Publishes QEMU RV64 service evidence keys for serial console, SSH banner,
  SSH probe, HTTP status code, HTTP probe, GPU readback, and WM marker.
- Publishes WM/RenderDoc evidence keys that require RDOC magic, Vulkan
  Engine2D, Simple2D readback, QEMU GPU/WM evidence, host WM evidence, and
  structured comparison.
- Publishes structured WM comparison keys for QEMU/host scene identity,
  window counts, focus IDs, titlebar/taskbar status, RenderDoc log compare,
  ARGB diff status, and zero mismatch count.
- Publishes Simple2D/Engine2D Vulkan keys for backend, scene, Simple2D command
  status, Vulkan device name, viewport, checksum, nonblank readback, and QEMU
  GPU readback.
- Publishes a QEMU SimpleOS Engine2D/Vulkan bridge plan requiring
  `qemu-riscv64-desktop`, `virtio_gpu` framebuffer drawing,
  `vulkan` Engine2D processing, `draw_ir-to-engine2d` Simple2D commands,
  device readback, QMP screendump readback, `capture-simple`, and the
  `simpleos-desktop-four-windows` WM comparison scene.
- Publishes RenderDoc artifact keys for `capture-simple`, `.rdc` path, raw
  `RDOC` magic plus `simpleos_renderdoc_rdc_magic_status`, payload size,
  capture log, Vulkan Engine2D metadata, helper status, and QEMU/host WM
  RenderDoc log paths.
- Publishes an aggregate live evidence gate that fails closed unless QEMU
  services, FPGA serial, Engine2D Vulkan, RenderDoc artifacts, structured WM
  comparison, and WM RenderDoc statuses all pass.
- Adds `scripts/check/check_simpleos_multiconfig_live_evidence.spl` as the
  aggregate status emitter; with no live artifacts it reports
  `blocked:qemu-service:blocked:missing-qemu-serial-console`.
- The checker also accepts `--evidence <path>` /
  `SIMPLEOS_MULTICONFIG_EVIDENCE`; future live wrappers should write the six
  aggregate `key=value` status rows there.
- The same evidence file may contain raw per-lane probe rows instead; the
  checker derives QEMU service, FPGA serial, Engine2D Vulkan, RenderDoc
  artifact, structured WM compare, and WM RenderDoc statuses from them.
- Adds Windows QEMU RV64 preflight wrapper
  `scripts/check/check-simpleos-qemu-rv64-desktop-evidence.ps1`, writing raw
  QEMU service rows to
  `build/simpleos_multiconfig_live_evidence/qemu-rv64-desktop.env`. It now also
  emits canonical, legacy-smoke, FPGA, and storage-probe artifact diagnostics
  while keeping the desktop gate tied to canonical SMF-FS/FAT32 artifacts and
  live serial/SSH/HTTP/GPU/WM probes.
- The same wrapper supports `-RunLiveBoot` once canonical artifacts exist. It
  launches QEMU, records a serial log under
  `build/os/systest/qemu-riscv64-desktop/`, probes SSH `2222` and HTTP `8080`,
  exposes QMP on `127.0.0.1:4444`, and validates a nonblank QMP `screendump`
  PPM before treating QEMU GPU readback as proven. Structured WM compare and
  RenderDoc remain separate gates.
- The same wrapper supports `-BuildDesktopServiceKernel`; on 2026-06-26 the
  rebuild-and-live path passed serial, SSH banner, HTTP `200`, QMP screendump
  nonblank GPU readback, and WM marker rows for
  `build/os/simpleos_riscv64_desktop_service.elf`.
- Adds Windows FPGA RV64 serial wrapper
  `scripts/check/check-simpleos-fpga-rv64-serial-evidence.ps1`, writing raw
  UART, serial boot marker, toolchain, bitstream, and blocked non-serial
  capability rows to
  `build/simpleos_multiconfig_live_evidence/fpga-rv64-serial.env`.
  It also supports `-BuildFpgaSerialKernel`, which builds
  `examples/09_embedded/simple_os/arch/riscv64/fpga_serial_entry.spl` to
  `build/os/simpleos_riscv64_fpga.elf` and records FPGA build rows before
  UART evidence is checked.
- Adds Windows WM host-compare wrapper
  `scripts/check/check-simpleos-wm-host-compare-evidence.ps1`; it merges base
  QEMU evidence with QEMU/host PPM comparison, RenderDoc `.rdc` magic, capture
  logs, and QEMU/host WM RenderDoc log rows for the aggregate checker. It keeps
  WM scene identity (`simpleos-desktop-four-windows`) separate from the
  RenderDoc/Engine2D scene (`vulkan-engine2d`). With `-AttemptHostWmCapture`,
  it also invokes the existing hosted-WM capture entrypoint and records
  attempt/status/exit/log rows without treating a crash or fallback as host-WM
  proof.
- Adds Windows Engine2D/RenderDoc normalizer
  `scripts/check/check-simpleos-engine2d-renderdoc-evidence.ps1`; it merges
  previous evidence with Engine2D Vulkan backend/readback rows and SimpleOS
  RenderDoc `.rdc` artifact rows. It also emits the QEMU SimpleOS
  Engine2D/Vulkan bridge rows; the aggregate checker prints
  `simpleos_engine2d_vulkan_bridge_status` as a fail-closed diagnostic. When
  the QEMU screendump PPM is present, it also records QEMU readback
  width/height/dimension-status rows and can use those dimensions as fallback
  viewport metadata; Vulkan backend proof is still required separately.
- `-ProbeHostVulkan` on the Engine2D/RenderDoc normalizer, or on the combined
  Windows wrapper, adds host readiness diagnostics for `vulkaninfo`, SDK tools,
  Chrome, Electron, RenderDoc tools, and focused browser-backing rows. Current
  host evidence: Vulkan runtime/device discovery passes with instance
  `1.3.301` on `Intel(R) UHD Graphics 770`, but SDK tools and RenderDoc are
  missing and `gui_web_2d_vulkan_browser_backing_status=fail`, so these rows
  are diagnostics only.
- Adds Windows combined evidence wrapper
  `scripts/check/check-simpleos-multiconfig-live-evidence.ps1`; it chains the
  QEMU, FPGA, WM compare, and Engine2D/RenderDoc wrappers, writes
  `build/simpleos_multiconfig_live_evidence/simpleos-multiconfig-live.env`,
  and returns the aggregate checker exit code. On the current host it is
  expected to remain blocked on missing live QEMU/FPGA/Vulkan/RenderDoc/WM
  artifacts.
- The aggregate checker now echoes Windows wrapper diagnostics from merged
  evidence files: wrapper name, QEMU/FPGA/WM/Engine2D child exit codes,
  aggregate status, and aggregate exit code.
- `-AttemptBuild` on the QEMU or combined Windows wrapper attempts
  `src\compiler_rust\target\debug\simple.exe os build --arch=riscv64`, writes
  `build/os/systest/qemu-riscv64-desktop/rv64-build.log`, and echoes build
  status rows through the aggregate checker. The wrapper now records the nested
  Simple binary, build backend, compiler, canonical artifact statuses, and
  optional disk-image builder rows. Current passing Windows build evidence uses
  `-BuildBackend cranelift` with
  `-BuildCc C:\dev\install\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin\clang.exe`,
  produces `build/os/simpleos_riscv64_smf_fs.elf`, and with
  `-BuildDiskImage` produces `build/os/fat32-riscv64.img`.
- `-BuildDesktopServiceKernel -RunLiveBoot` now makes the QEMU service gate
  pass. The combined aggregate still exits nonzero, now first blocked at
  `blocked:fpga-serial:blocked:missing-fpga-uart-terminal`, with Engine2D
  Vulkan, RenderDoc, host-WM, and structured comparison evidence still open.
- `-AttemptHostWmCapture` currently records hosted-WM capture failure on this
  Windows debug driver as `blocked:host-capture-exit-neg1073741819`, leaving
  `simpleos_wm_structured_compare_evidence_status=blocked:missing-host-wm-scene`.

Completion blockers:
- FPGA UART serial device/boot marker/toolchain/bitstream evidence on hardware
  (the serial-only FPGA ELF now builds locally).
- Engine2D Vulkan proof.
- SimpleOS RenderDoc `.rdc` with `RDOC` magic.
- QEMU WM vs host WM comparison report.
- Windows Vulkan SDK tools, RenderDoc tools, and focused browser-backing proof
  before any browser or host RenderDoc Vulkan claim can pass.
