# SimpleOS Multi-Config Vulkan WM Contract

> This scenario manual verifies the static, non-hardware contract for the SimpleOS multi-config hardening lane. QEMU RV64 is the desktop/service/GPU profile. FPGA RV64 remains UART serial-only until hardware evidence expands it. The RenderDoc/WM comparison contract is fail-closed and requires real RDOC, Vulkan Engine2D, Simple2D readback, QEMU WM evidence, host WM evidence, and a structured comparison report before completion.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Multi-Config Vulkan WM Contract

This scenario manual verifies the static, non-hardware contract for the SimpleOS multi-config hardening lane. QEMU RV64 is the desktop/service/GPU profile. FPGA RV64 remains UART serial-only until hardware evidence expands it. The RenderDoc/WM comparison contract is fail-closed and requires real RDOC, Vulkan Engine2D, Simple2D readback, QEMU WM evidence, host WM evidence, and a structured comparison report before completion.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | simpleos-multiconfig-vulkan-wm |
| Category | OS / QEMU / FPGA / GPU / WM |
| Status | In Progress |
| Plan | doc/03_plan/os/simpleos_multiconfig_vulkan_wm_plan.md |
| Source | `test/01_unit/os/simpleos_config_matrix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This scenario manual verifies the static, non-hardware contract for the
SimpleOS multi-config hardening lane. QEMU RV64 is the desktop/service/GPU
profile. FPGA RV64 remains UART serial-only until hardware evidence expands it.
The RenderDoc/WM comparison contract is fail-closed and requires real RDOC,
Vulkan Engine2D, Simple2D readback, QEMU WM evidence, host WM evidence, and a
structured comparison report before completion.

## Scenarios

### SimpleOS multi-config Vulkan WM contract

#### defines QEMU RV64 desktop as the service GPU WM Vulkan profile

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines QEMU RV64 desktop as the service GPU WM Vulkan profile
   - Expected: loaded equals `qemu-riscv64-desktop`
   - Expected: profile.name equals `qemu-riscv64-desktop`
   - Expected: profile.arch equals `riscv64`
   - Expected: profile.ssh_endpoint() equals `127.0.0.1:2222`
   - Expected: profile.http_endpoint() equals `127.0.0.1:8080`
   - Expected: qemu_riscv64_desktop_ssh_endpoint() equals `127.0.0.1:2222`
   - Expected: qemu_riscv64_desktop_http_endpoint() equals `127.0.0.1:8080`
   - Expected: profile_requirement_status(profile, capability) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("defines QEMU RV64 desktop as the service GPU WM Vulkan profile")
val loaded = load_qemu_rv64_desktop_profile()
expect(loaded).to_equal("qemu-riscv64-desktop")
val profile = qemu_riscv64_desktop_profile()
expect(profile.name).to_equal("qemu-riscv64-desktop")
expect(profile.arch).to_equal("riscv64")
expect(profile.ssh_endpoint()).to_equal("127.0.0.1:2222")
expect(profile.http_endpoint()).to_equal("127.0.0.1:8080")
expect(qemu_riscv64_desktop_ssh_endpoint()).to_equal("127.0.0.1:2222")
expect(qemu_riscv64_desktop_http_endpoint()).to_equal("127.0.0.1:8080")
for capability in qemu_riscv64_required_capabilities():
    expect(profile_requirement_status(profile, capability)).to_equal("ready")
```

</details>

#### keeps FPGA RV64 serial-only and fail-closed for desktop capabilities

- keeps FPGA RV64 serial-only and fail-closed for desktop capabilities
   - Expected: loaded equals `fpga-riscv64-serial`
   - Expected: profile.name equals `fpga-riscv64-serial`
   - Expected: profile.arch equals `riscv64`
   - Expected: profile.terminal_kind equals `uart-serial`
   - Expected: fpga_riscv64_serial_entry_path() equals `examples/09_embedded/simple_os/arch/riscv64/fpga_serial_entry.spl`
   - Expected: fpga_riscv64_serial_kernel_path() equals `build/os/simpleos_riscv64_fpga.elf`
   - Expected: fpga_riscv64_serial_boot_marker() equals `SIMPLEOS_FPGA_RISCV64_SERIAL_BOOT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps FPGA RV64 serial-only and fail-closed for desktop capabilities")
val loaded = load_fpga_rv64_serial_profile()
expect(loaded).to_equal("fpga-riscv64-serial")
val profile = fpga_riscv64_serial_profile()
expect(profile.name).to_equal("fpga-riscv64-serial")
expect(profile.arch).to_equal("riscv64")
expect(profile.terminal_kind).to_equal("uart-serial")
expect(fpga_riscv64_serial_entry_path()).to_equal("examples/09_embedded/simple_os/arch/riscv64/fpga_serial_entry.spl")
expect(fpga_riscv64_serial_kernel_path()).to_equal("build/os/simpleos_riscv64_fpga.elf")
expect(fpga_riscv64_serial_boot_marker()).to_equal("SIMPLEOS_FPGA_RISCV64_SERIAL_BOOT")
assert_true(profile_supports_capability(profile, "serial-terminal"))
for capability in [
    "ssh",
    "http",
    "gpu",
    "framebuffer",
    "wm",
    "simple2d-engine2d",
    "vulkan",
    "renderdoc",
    "host-wm-compare"
]:
    val status = profile_requirement_status(profile, capability)
    expect(status).to_contain("blocked:fpga-riscv64-currently-uart-serial-only:")
```

</details>

#### requires FPGA RV64 UART serial evidence and blocks desktop capabilities

- requires FPGA RV64 UART serial evidence and blocks desktop capabilities
   - Expected: fpga_status equals `pass`
   - Expected: simpleos_fpga_serial_status(pass_evidence) equals `pass`
   - Expected: simpleos_fpga_serial_status(missing_uart) equals `blocked:missing-fpga-uart-terminal`
   - Expected: simpleos_fpga_serial_status(ssh_enabled) equals `blocked:fpga-ssh-must-remain-blocked`
   - Expected: simpleos_fpga_serial_status(gpu_enabled) equals `blocked:fpga-gpu-must-remain-blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 70 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires FPGA RV64 UART serial evidence and blocks desktop capabilities")
val fpga_status = read_fpga_serial_contract_status()
expect(fpga_status).to_equal("pass")
val keys = simpleos_fpga_serial_required_evidence_keys()
assert_true(text_list_contains_value(keys, "simpleos_fpga_board_profile"))
assert_true(text_list_contains_value(keys, "simpleos_fpga_expected_entry"))
assert_true(text_list_contains_value(keys, "simpleos_fpga_expected_kernel_path"))
assert_true(text_list_contains_value(keys, "simpleos_fpga_uart_terminal_status"))
assert_true(text_list_contains_value(keys, "simpleos_fpga_serial_device"))
assert_true(text_list_contains_value(keys, "simpleos_fpga_serial_boot_marker"))
assert_true(text_list_contains_value(keys, "simpleos_fpga_toolchain_status"))
assert_true(text_list_contains_value(keys, "simpleos_fpga_bitstream_status"))
assert_true(text_list_contains_value(keys, "simpleos_fpga_ssh_status"))
assert_true(text_list_contains_value(keys, "simpleos_fpga_http_status"))
assert_true(text_list_contains_value(keys, "simpleos_fpga_gpu_status"))
assert_true(text_list_contains_value(keys, "simpleos_fpga_wm_status"))
assert_true(text_list_contains_value(keys, "simpleos_fpga_vulkan_status"))
assert_true(text_list_contains_value(keys, "simpleos_fpga_renderdoc_status"))

val pass_evidence = passing_simpleos_fpga_serial_evidence()
expect(simpleos_fpga_serial_status(pass_evidence)).to_equal("pass")

val missing_uart = SimpleOsFpgaSerialEvidence(
    board_profile: "fpga-riscv64-serial",
    uart_terminal_status: "missing",
    serial_device: "uart0",
    serial_boot_marker: "SIMPLEOS_FPGA_RISCV64_SERIAL_BOOT",
    toolchain_status: "pass",
    bitstream_status: "pass",
    ssh_status: "blocked",
    http_status: "blocked",
    gpu_status: "blocked",
    wm_status: "blocked",
    vulkan_status: "blocked",
    renderdoc_status: "blocked"
)
expect(simpleos_fpga_serial_status(missing_uart)).to_equal("blocked:missing-fpga-uart-terminal")

val ssh_enabled = SimpleOsFpgaSerialEvidence(
    board_profile: "fpga-riscv64-serial",
    uart_terminal_status: "pass",
    serial_device: "uart0",
    serial_boot_marker: "SIMPLEOS_FPGA_RISCV64_SERIAL_BOOT",
    toolchain_status: "pass",
    bitstream_status: "pass",
    ssh_status: "pass",
    http_status: "blocked",
    gpu_status: "blocked",
    wm_status: "blocked",
    vulkan_status: "blocked",
    renderdoc_status: "blocked"
)
expect(simpleos_fpga_serial_status(ssh_enabled)).to_equal("blocked:fpga-ssh-must-remain-blocked")

val gpu_enabled = SimpleOsFpgaSerialEvidence(
    board_profile: "fpga-riscv64-serial",
    uart_terminal_status: "pass",
    serial_device: "uart0",
    serial_boot_marker: "SIMPLEOS_FPGA_RISCV64_SERIAL_BOOT",
    toolchain_status: "pass",
    bitstream_status: "pass",
    ssh_status: "blocked",
    http_status: "blocked",
    gpu_status: "pass",
    wm_status: "blocked",
    vulkan_status: "blocked",
    renderdoc_status: "blocked"
)
expect(simpleos_fpga_serial_status(gpu_enabled)).to_equal("blocked:fpga-gpu-must-remain-blocked")
```

</details>

#### publishes QEMU RV64 desktop launch args with service ports and GPU

- publishes QEMU RV64 desktop launch args with service ports and GPU
   - Expected: launch_status equals `ready`
   - Expected: qemu_riscv64_desktop_artifact_dir() equals `build/os/systest/qemu-riscv64-desktop`
   - Expected: qemu_riscv64_desktop_qemu_args_status(args) equals `ready`
   - Expected: riscv64_desktop_qemu_args_status() equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("publishes QEMU RV64 desktop launch args with service ports and GPU")
val launch_status = read_qemu_rv64_desktop_launch_status()
expect(launch_status).to_equal("ready")
val args = qemu_riscv64_desktop_qemu_args()
expect(qemu_riscv64_desktop_artifact_dir()).to_equal("build/os/systest/qemu-riscv64-desktop")
expect(qemu_riscv64_desktop_qemu_args_status(args)).to_equal("ready")
expect(riscv64_desktop_qemu_args_status()).to_equal("ready")
assert_true(text_list_contains_value(riscv64_desktop_qemu_args(), "virtio-gpu-pci,disable-modern=on,disable-legacy=off"))
assert_true(text_list_contains_value(args, "user,id=rvnet,hostfwd=tcp::2222-:22,hostfwd=tcp::8080-:8080"))
assert_true(text_list_contains_value(args, "virtio-net-pci,netdev=rvnet"))
assert_true(text_list_contains_value(args, "virtio-gpu-pci,disable-modern=on,disable-legacy=off"))
assert_true(text_list_contains_value(args, "none"))
assert_true(text_list_contains_value(args, "tcp:127.0.0.1:4444,server,nowait"))
```

</details>

#### requires live QEMU SSH HTTP GPU and WM service evidence

- requires live QEMU SSH HTTP GPU and WM service evidence
   - Expected: service_status equals `pass`
   - Expected: simpleos_qemu_service_evidence_status(pass_evidence) equals `pass`
   - Expected: simpleos_qemu_service_evidence_status(missing_ssh) equals `blocked:missing-qemu-ssh-banner`
   - Expected: simpleos_qemu_service_evidence_status(missing_gpu) equals `blocked:missing-qemu-gpu-readback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires live QEMU SSH HTTP GPU and WM service evidence")
val service_status = read_qemu_rv64_service_evidence_contract_status()
expect(service_status).to_equal("pass")
val keys = simpleos_qemu_service_required_evidence_keys()
assert_true(text_list_contains_value(keys, "simpleos_qemu_serial_console_status"))
assert_true(text_list_contains_value(keys, "simpleos_qemu_rv64_ssh_banner"))
assert_true(text_list_contains_value(keys, "simpleos_qemu_rv64_ssh_probe_status"))
assert_true(text_list_contains_value(keys, "simpleos_qemu_rv64_http_status_code"))
assert_true(text_list_contains_value(keys, "simpleos_qemu_rv64_http_probe_status"))
assert_true(text_list_contains_value(keys, "simpleos_qemu_gpu_readback_status"))
assert_true(text_list_contains_value(keys, "simpleos_qemu_wm_marker_status"))

val pass_evidence = passing_simpleos_qemu_service_evidence()
expect(simpleos_qemu_service_evidence_status(pass_evidence)).to_equal("pass")

val missing_ssh = SimpleOsQemuServiceEvidence(
    serial_console_status: "pass",
    ssh_banner: "",
    ssh_probe_status: "pass",
    http_status_code: 200,
    http_probe_status: "pass",
    gpu_readback_status: "pass",
    wm_marker_status: "pass"
)
expect(simpleos_qemu_service_evidence_status(missing_ssh)).to_equal("blocked:missing-qemu-ssh-banner")

val missing_gpu = SimpleOsQemuServiceEvidence(
    serial_console_status: "pass",
    ssh_banner: "SSH-2.0-SimpleOS",
    ssh_probe_status: "pass",
    http_status_code: 200,
    http_probe_status: "pass",
    gpu_readback_status: "missing",
    wm_marker_status: "pass"
)
expect(simpleos_qemu_service_evidence_status(missing_gpu)).to_equal("blocked:missing-qemu-gpu-readback")
```

</details>

#### requires structured QEMU host WM comparison evidence

- requires structured QEMU host WM comparison evidence
   - Expected: compare_status equals `pass`
   - Expected: simpleos_wm_structured_compare_status(pass_evidence) equals `pass`
   - Expected: simpleos_wm_structured_compare_status(scene_mismatch) equals `blocked:wm-scene-mismatch`
   - Expected: simpleos_wm_structured_compare_status(missing_log_compare) equals `blocked:missing-renderdoc-log-compare`
   - Expected: simpleos_wm_structured_compare_status(pixel_mismatch) equals `blocked:wm-argb-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 68 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires structured QEMU host WM comparison evidence")
val compare_status = read_wm_structured_compare_contract_status()
expect(compare_status).to_equal("pass")
val keys = simpleos_wm_structured_compare_required_evidence_keys()
assert_true(text_list_contains_value(keys, "simpleos_wm_qemu_scene"))
assert_true(text_list_contains_value(keys, "simpleos_wm_host_scene"))
assert_true(text_list_contains_value(keys, "simpleos_wm_qemu_window_count"))
assert_true(text_list_contains_value(keys, "simpleos_wm_host_window_count"))
assert_true(text_list_contains_value(keys, "simpleos_wm_qemu_focus_id"))
assert_true(text_list_contains_value(keys, "simpleos_wm_host_focus_id"))
assert_true(text_list_contains_value(keys, "simpleos_wm_renderdoc_log_compare_status"))
assert_true(text_list_contains_value(keys, "simpleos_wm_argb_diff_status"))
assert_true(text_list_contains_value(keys, "simpleos_wm_argb_mismatch_count"))

val pass_evidence = passing_simpleos_wm_structured_compare_evidence()
expect(simpleos_wm_structured_compare_status(pass_evidence)).to_equal("pass")

val scene_mismatch = SimpleOsWmStructuredCompareEvidence(
    qemu_scene: "simpleos-desktop-four-windows",
    host_scene: "host-other-scene",
    qemu_window_count: 4,
    host_window_count: 4,
    qemu_focus_id: "window-1",
    host_focus_id: "window-1",
    qemu_titlebar_status: "pass",
    host_titlebar_status: "pass",
    qemu_taskbar_status: "pass",
    host_taskbar_status: "pass",
    renderdoc_log_compare_status: "pass",
    argb_diff_status: "pass",
    argb_mismatch_count: 0
)
expect(simpleos_wm_structured_compare_status(scene_mismatch)).to_equal("blocked:wm-scene-mismatch")

val missing_log_compare = SimpleOsWmStructuredCompareEvidence(
    qemu_scene: "simpleos-desktop-four-windows",
    host_scene: "simpleos-desktop-four-windows",
    qemu_window_count: 4,
    host_window_count: 4,
    qemu_focus_id: "window-1",
    host_focus_id: "window-1",
    qemu_titlebar_status: "pass",
    host_titlebar_status: "pass",
    qemu_taskbar_status: "pass",
    host_taskbar_status: "pass",
    renderdoc_log_compare_status: "missing",
    argb_diff_status: "pass",
    argb_mismatch_count: 0
)
expect(simpleos_wm_structured_compare_status(missing_log_compare)).to_equal("blocked:missing-renderdoc-log-compare")

val pixel_mismatch = SimpleOsWmStructuredCompareEvidence(
    qemu_scene: "simpleos-desktop-four-windows",
    host_scene: "simpleos-desktop-four-windows",
    qemu_window_count: 4,
    host_window_count: 4,
    qemu_focus_id: "window-1",
    host_focus_id: "window-1",
    qemu_titlebar_status: "pass",
    host_titlebar_status: "pass",
    qemu_taskbar_status: "pass",
    host_taskbar_status: "pass",
    renderdoc_log_compare_status: "pass",
    argb_diff_status: "pass",
    argb_mismatch_count: 7
)
expect(simpleos_wm_structured_compare_status(pixel_mismatch)).to_equal("blocked:wm-argb-mismatch")
```

</details>

#### requires Simple2D over Engine2D Vulkan readback evidence

- requires Simple2D over Engine2D Vulkan readback evidence
   - Expected: engine_status equals `pass`
   - Expected: simpleos_engine2d_vulkan_status(pass_evidence) equals `pass`
   - Expected: simpleos_engine2d_vulkan_status(cpu_fallback) equals `blocked:missing-engine2d-vulkan-backend`
   - Expected: simpleos_engine2d_vulkan_status(missing_checksum) equals `blocked:missing-engine2d-readback-checksum`
   - Expected: simpleos_engine2d_vulkan_status(missing_qemu_gpu) equals `blocked:missing-qemu-gpu-readback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 56 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires Simple2D over Engine2D Vulkan readback evidence")
val engine_status = read_engine2d_vulkan_contract_status()
expect(engine_status).to_equal("pass")
val keys = simpleos_engine2d_vulkan_required_evidence_keys()
assert_true(text_list_contains_value(keys, "simpleos_engine2d_runtime_backend"))
assert_true(text_list_contains_value(keys, "simpleos_engine2d_scene"))
assert_true(text_list_contains_value(keys, "simpleos_simple2d_command_status"))
assert_true(text_list_contains_value(keys, "simpleos_engine2d_vulkan_device_name"))
assert_true(text_list_contains_value(keys, "simpleos_engine2d_viewport_width"))
assert_true(text_list_contains_value(keys, "simpleos_engine2d_viewport_height"))
assert_true(text_list_contains_value(keys, "simpleos_engine2d_readback_checksum"))
assert_true(text_list_contains_value(keys, "simpleos_engine2d_readback_nonblank_status"))
assert_true(text_list_contains_value(keys, "simpleos_qemu_gpu_readback_status"))

val pass_evidence = passing_simpleos_engine2d_vulkan_evidence()
expect(simpleos_engine2d_vulkan_status(pass_evidence)).to_equal("pass")

val cpu_fallback = SimpleOsEngine2dVulkanEvidence(
    runtime_backend: "cpu",
    engine_scene: "vulkan-engine2d",
    simple2d_command_status: "pass",
    device_name: "qemu-virtio-vulkan",
    viewport_width: 800,
    viewport_height: 600,
    readback_checksum: "engine2d-vulkan-readback-checksum",
    readback_nonblank_status: "pass",
    qemu_gpu_readback_status: "pass"
)
expect(simpleos_engine2d_vulkan_status(cpu_fallback)).to_equal("blocked:missing-engine2d-vulkan-backend")

val missing_checksum = SimpleOsEngine2dVulkanEvidence(
    runtime_backend: "vulkan",
    engine_scene: "vulkan-engine2d",
    simple2d_command_status: "pass",
    device_name: "qemu-virtio-vulkan",
    viewport_width: 800,
    viewport_height: 600,
    readback_checksum: "",
    readback_nonblank_status: "pass",
    qemu_gpu_readback_status: "pass"
)
expect(simpleos_engine2d_vulkan_status(missing_checksum)).to_equal("blocked:missing-engine2d-readback-checksum")

val missing_qemu_gpu = SimpleOsEngine2dVulkanEvidence(
    runtime_backend: "vulkan",
    engine_scene: "vulkan-engine2d",
    simple2d_command_status: "pass",
    device_name: "qemu-virtio-vulkan",
    viewport_width: 800,
    viewport_height: 600,
    readback_checksum: "engine2d-vulkan-readback-checksum",
    readback_nonblank_status: "pass",
    qemu_gpu_readback_status: "missing"
)
expect(simpleos_engine2d_vulkan_status(missing_qemu_gpu)).to_equal("blocked:missing-qemu-gpu-readback")
```

</details>

#### defines the QEMU SimpleOS Engine2D Vulkan bridge path

- defines the QEMU SimpleOS Engine2D Vulkan bridge path
   - Expected: bridge_status equals `ready`
   - Expected: plan.profile_name equals `qemu-riscv64-desktop`
   - Expected: plan.drawing_backend equals `virtio_gpu`
   - Expected: plan.processing_backend equals `vulkan`
   - Expected: plan.qemu_gpu_device equals `virtio-gpu-pci,disable-modern=on,disable-legacy=off`
   - Expected: plan.scene_name equals `vulkan-engine2d`
   - Expected: plan.simple2d_command_path equals `draw_ir-to-engine2d`
   - Expected: plan.renderdoc_capture_mode equals `capture-simple`
   - Expected: plan.wm_compare_scene equals `simpleos-desktop-four-windows`
   - Expected: simpleos_engine2d_vulkan_bridge_plan_status(cpu_fallback) equals `blocked:missing-engine2d-vulkan-processing-backend`
   - Expected: simpleos_engine2d_vulkan_bridge_plan_status(missing_qmp) equals `blocked:missing-qemu-qmp-screendump-requirement`


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("defines the QEMU SimpleOS Engine2D Vulkan bridge path")
val bridge_status = read_engine2d_vulkan_bridge_plan_status()
expect(bridge_status).to_equal("ready")
val keys = simpleos_engine2d_vulkan_bridge_required_keys()
assert_true(text_list_contains_value(keys, "simpleos_engine2d_bridge_profile"))
assert_true(text_list_contains_value(keys, "simpleos_engine2d_drawing_backend"))
assert_true(text_list_contains_value(keys, "simpleos_engine2d_processing_backend"))
assert_true(text_list_contains_value(keys, "simpleos_engine2d_qemu_gpu_device"))
assert_true(text_list_contains_value(keys, "simpleos_simple2d_command_path"))
assert_true(text_list_contains_value(keys, "simpleos_qemu_qmp_screendump_required"))
assert_true(text_list_contains_value(keys, "simpleos_renderdoc_capture_mode"))

val plan = qemu_riscv64_engine2d_vulkan_bridge_plan()
expect(plan.profile_name).to_equal("qemu-riscv64-desktop")
expect(plan.drawing_backend).to_equal("virtio_gpu")
expect(plan.processing_backend).to_equal("vulkan")
expect(plan.qemu_gpu_device).to_equal("virtio-gpu-pci,disable-modern=on,disable-legacy=off")
expect(plan.scene_name).to_equal("vulkan-engine2d")
expect(plan.simple2d_command_path).to_equal("draw_ir-to-engine2d")
assert_true(plan.requires_device_readback)
assert_true(plan.requires_qmp_screendump)
expect(plan.renderdoc_capture_mode).to_equal("capture-simple")
expect(plan.wm_compare_scene).to_equal("simpleos-desktop-four-windows")

val cpu_fallback = SimpleOsEngine2dVulkanBridgePlan(
    profile_name: "qemu-riscv64-desktop",
    drawing_backend: "virtio_gpu",
    processing_backend: "cpu",
    qemu_gpu_device: "virtio-gpu-pci,disable-modern=on,disable-legacy=off",
    scene_name: "vulkan-engine2d",
    simple2d_command_path: "draw_ir-to-engine2d",
    requires_device_readback: true,
    requires_qmp_screendump: true,
    renderdoc_capture_mode: "capture-simple",
    wm_compare_scene: "simpleos-desktop-four-windows"
)
expect(simpleos_engine2d_vulkan_bridge_plan_status(cpu_fallback)).to_equal("blocked:missing-engine2d-vulkan-processing-backend")

val missing_qmp = SimpleOsEngine2dVulkanBridgePlan(
    profile_name: "qemu-riscv64-desktop",
    drawing_backend: "virtio_gpu",
    processing_backend: "vulkan",
    qemu_gpu_device: "virtio-gpu-pci,disable-modern=on,disable-legacy=off",
    scene_name: "vulkan-engine2d",
    simple2d_command_path: "draw_ir-to-engine2d",
    requires_device_readback: true,
    requires_qmp_screendump: false,
    renderdoc_capture_mode: "capture-simple",
    wm_compare_scene: "simpleos-desktop-four-windows"
)
expect(simpleos_engine2d_vulkan_bridge_plan_status(missing_qmp)).to_equal("blocked:missing-qemu-qmp-screendump-requirement")
```

</details>

#### audits current QEMU Engine2D source wiring without promoting it to Vulkan proof

- audits current QEMU Engine2D source wiring without promoting it to Vulkan proof
   - Expected: audit_status equals `blocked:desktop-service-not-wired-to-vulkan-engine2d-session`
   - Expected: simpleos_engine2d_source_bridge_audit_status(missing_vulkan_session) equals `blocked:missing-engine2d-vulkan-session`
   - Expected: simpleos_engine2d_source_bridge_audit_status(wrong_draw_path) equals `blocked:unknown-qemu-draw-path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("audits current QEMU Engine2D source wiring without promoting it to Vulkan proof")
val audit_status = read_engine2d_source_bridge_audit_status()
expect(audit_status).to_equal("blocked:desktop-service-not-wired-to-vulkan-engine2d-session")
val keys = simpleos_engine2d_source_bridge_audit_required_keys()
assert_true(text_list_contains_value(keys, "simpleos_engine2d_source_qemu_entry_status"))
assert_true(text_list_contains_value(keys, "simpleos_engine2d_source_baremetal_core_status"))
assert_true(text_list_contains_value(keys, "simpleos_engine2d_source_virtio_surface_status"))
assert_true(text_list_contains_value(keys, "simpleos_engine2d_source_vulkan_session_status"))
assert_true(text_list_contains_value(keys, "simpleos_engine2d_source_current_draw_path"))
assert_true(text_list_contains_value(keys, "simpleos_engine2d_source_target_processing_backend"))
assert_true(text_list_contains_value(keys, "simpleos_engine2d_source_bridge_audit_status"))

val missing_vulkan_session = SimpleOsEngine2dSourceBridgeAudit(
    qemu_entry_status: "pass",
    baremetal_core_status: "pass",
    virtio_surface_status: "pass",
    vulkan_session_status: "missing",
    current_draw_path: "freestanding-display-runtime",
    target_processing_backend: "vulkan"
)
expect(simpleos_engine2d_source_bridge_audit_status(missing_vulkan_session)).to_equal("blocked:missing-engine2d-vulkan-session")

val wrong_draw_path = SimpleOsEngine2dSourceBridgeAudit(
    qemu_entry_status: "pass",
    baremetal_core_status: "pass",
    virtio_surface_status: "pass",
    vulkan_session_status: "pass",
    current_draw_path: "host-only-fixture",
    target_processing_backend: "vulkan"
)
expect(simpleos_engine2d_source_bridge_audit_status(wrong_draw_path)).to_equal("blocked:unknown-qemu-draw-path")
```

</details>

#### requires RenderDoc artifact RDOC magic and WM logs

- requires RenderDoc artifact RDOC magic and WM logs
   - Expected: artifact_status equals `pass`
   - Expected: simpleos_renderdoc_artifact_status(pass_evidence) equals `pass`
   - Expected: simpleos_renderdoc_artifact_status(wrong_mode) equals `blocked:missing-renderdoc-capture-simple-mode`
   - Expected: simpleos_renderdoc_artifact_status(missing_magic) equals `blocked:missing-simple-rdoc-magic`
   - Expected: simpleos_renderdoc_artifact_status(tiny_capture) equals `blocked:missing-simple-rdoc-payload`
   - Expected: simpleos_renderdoc_artifact_status(missing_host_log) equals `blocked:missing-host-wm-renderdoc-log`


<details>
<summary>Executable SSpec</summary>

Runnable source: 80 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires RenderDoc artifact RDOC magic and WM logs")
val artifact_status = read_renderdoc_artifact_contract_status()
expect(artifact_status).to_equal("pass")
val keys = simpleos_renderdoc_artifact_required_evidence_keys()
assert_true(text_list_contains_value(keys, "simpleos_renderdoc_capture_mode"))
assert_true(text_list_contains_value(keys, "simpleos_renderdoc_rdc_path"))
assert_true(text_list_contains_value(keys, "simpleos_renderdoc_rdc_magic"))
assert_true(text_list_contains_value(keys, "simpleos_renderdoc_rdc_magic_status"))
assert_true(text_list_contains_value(keys, "simpleos_renderdoc_rdc_size_bytes"))
assert_true(text_list_contains_value(keys, "simpleos_renderdoc_capture_log_path"))
assert_true(text_list_contains_value(keys, "simpleos_renderdoc_capture_log_status"))
assert_true(text_list_contains_value(keys, "simpleos_renderdoc_simple_runtime_backend"))
assert_true(text_list_contains_value(keys, "simpleos_renderdoc_simple_scene"))
assert_true(text_list_contains_value(keys, "simpleos_renderdoc_helper_status"))
assert_true(text_list_contains_value(keys, "simpleos_renderdoc_qemu_wm_log_path"))
assert_true(text_list_contains_value(keys, "simpleos_renderdoc_host_wm_log_path"))

val pass_evidence = passing_simpleos_renderdoc_artifact_evidence()
expect(simpleos_renderdoc_artifact_status(pass_evidence)).to_equal("pass")

val wrong_mode = SimpleOsRenderdocArtifactEvidence(
    capture_mode: "capture-html",
    rdc_path: "build/os/systest/qemu-riscv64-desktop/simpleos-engine2d.rdc",
    rdc_magic: "RDOC",
    rdc_size_bytes: 4096,
    capture_log_path: "build/os/systest/qemu-riscv64-desktop/renderdoc-capture.log",
    capture_log_status: "pass",
    simple_runtime_backend: "vulkan",
    simple_scene: "vulkan-engine2d",
    renderdoc_helper_status: "pass",
    qemu_wm_log_path: "build/os/systest/qemu-riscv64-desktop/qemu-wm-renderdoc.log",
    host_wm_log_path: "build/os/systest/qemu-riscv64-desktop/host-wm-renderdoc.log"
)
expect(simpleos_renderdoc_artifact_status(wrong_mode)).to_equal("blocked:missing-renderdoc-capture-simple-mode")

val missing_magic = SimpleOsRenderdocArtifactEvidence(
    capture_mode: "capture-simple",
    rdc_path: "build/os/systest/qemu-riscv64-desktop/simpleos-engine2d.rdc",
    rdc_magic: "NOPE",
    rdc_size_bytes: 4096,
    capture_log_path: "build/os/systest/qemu-riscv64-desktop/renderdoc-capture.log",
    capture_log_status: "pass",
    simple_runtime_backend: "vulkan",
    simple_scene: "vulkan-engine2d",
    renderdoc_helper_status: "pass",
    qemu_wm_log_path: "build/os/systest/qemu-riscv64-desktop/qemu-wm-renderdoc.log",
    host_wm_log_path: "build/os/systest/qemu-riscv64-desktop/host-wm-renderdoc.log"
)
expect(simpleos_renderdoc_artifact_status(missing_magic)).to_equal("blocked:missing-simple-rdoc-magic")

val tiny_capture = SimpleOsRenderdocArtifactEvidence(
    capture_mode: "capture-simple",
    rdc_path: "build/os/systest/qemu-riscv64-desktop/simpleos-engine2d.rdc",
    rdc_magic: "RDOC",
    rdc_size_bytes: 4,
    capture_log_path: "build/os/systest/qemu-riscv64-desktop/renderdoc-capture.log",
    capture_log_status: "pass",
    simple_runtime_backend: "vulkan",
    simple_scene: "vulkan-engine2d",
    renderdoc_helper_status: "pass",
    qemu_wm_log_path: "build/os/systest/qemu-riscv64-desktop/qemu-wm-renderdoc.log",
    host_wm_log_path: "build/os/systest/qemu-riscv64-desktop/host-wm-renderdoc.log"
)
expect(simpleos_renderdoc_artifact_status(tiny_capture)).to_equal("blocked:missing-simple-rdoc-payload")

val missing_host_log = SimpleOsRenderdocArtifactEvidence(
    capture_mode: "capture-simple",
    rdc_path: "build/os/systest/qemu-riscv64-desktop/simpleos-engine2d.rdc",
    rdc_magic: "RDOC",
    rdc_size_bytes: 4096,
    capture_log_path: "build/os/systest/qemu-riscv64-desktop/renderdoc-capture.log",
    capture_log_status: "pass",
    simple_runtime_backend: "vulkan",
    simple_scene: "vulkan-engine2d",
    renderdoc_helper_status: "pass",
    qemu_wm_log_path: "build/os/systest/qemu-riscv64-desktop/qemu-wm-renderdoc.log",
    host_wm_log_path: ""
)
expect(simpleos_renderdoc_artifact_status(missing_host_log)).to_equal("blocked:missing-host-wm-renderdoc-log")
```

</details>

#### requires RenderDoc Vulkan Engine2D and QEMU host WM comparison evidence

- requires RenderDoc Vulkan Engine2D and QEMU host WM comparison evidence
   - Expected: contract_status equals `pass`
   - Expected: simpleos_wm_renderdoc_evidence_status(pass_evidence) equals `pass`
   - Expected: simpleos_wm_renderdoc_evidence_status(missing_rdoc) equals `blocked:missing-simple-rdoc-magic`
   - Expected: simpleos_wm_renderdoc_evidence_status(cpu_fallback) equals `blocked:missing-simple-vulkan-runtime`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires RenderDoc Vulkan Engine2D and QEMU host WM comparison evidence")
val contract_status = read_renderdoc_wm_evidence_contract_status()
expect(contract_status).to_equal("pass")
val keys = simpleos_wm_renderdoc_required_evidence_keys()
assert_true(text_list_contains_value(keys, "simpleos_renderdoc_rdc_magic_status"))
assert_true(text_list_contains_value(keys, "simpleos_renderdoc_simple_runtime_backend"))
assert_true(text_list_contains_value(keys, "simpleos_renderdoc_simple_scene"))
assert_true(text_list_contains_value(keys, "simpleos_simple2d_readback_status"))
assert_true(text_list_contains_value(keys, "simpleos_qemu_gpu_readback_status"))
assert_true(text_list_contains_value(keys, "simpleos_qemu_wm_evidence_status"))
assert_true(text_list_contains_value(keys, "simpleos_host_wm_evidence_status"))
assert_true(text_list_contains_value(keys, "simpleos_wm_qemu_host_compare_status"))

val pass_evidence = passing_simpleos_wm_renderdoc_evidence()
expect(simpleos_wm_renderdoc_evidence_status(pass_evidence)).to_equal("pass")

val missing_rdoc = SimpleOsWmRenderdocEvidence(
    simple_rdc_magic: "NOPE",
    simple_runtime_backend: "vulkan",
    simple_scene: "vulkan-engine2d",
    simple2d_readback_status: "pass",
    qemu_gpu_readback_status: "pass",
    qemu_wm_status: "pass",
    host_wm_status: "pass",
    structured_compare_status: "pass"
)
expect(simpleos_wm_renderdoc_evidence_status(missing_rdoc)).to_equal("blocked:missing-simple-rdoc-magic")

val cpu_fallback = SimpleOsWmRenderdocEvidence(
    simple_rdc_magic: "RDOC",
    simple_runtime_backend: "cpu",
    simple_scene: "vulkan-engine2d",
    simple2d_readback_status: "pass",
    qemu_gpu_readback_status: "pass",
    qemu_wm_status: "pass",
    host_wm_status: "pass",
    structured_compare_status: "pass"
)
expect(simpleos_wm_renderdoc_evidence_status(cpu_fallback)).to_equal("blocked:missing-simple-vulkan-runtime")
```

</details>

#### aggregates live evidence gates before completion

- aggregates live evidence gates before completion
   - Expected: live_status equals `pass`
   - Expected: simpleos_screen_required_evidence_keys().len() equals `28`
   - Expected: simpleos_multiconfig_live_status(pass_evidence) equals `pass`
   - Expected: simpleos_multiconfig_live_status(missing_qemu) equals `blocked:qemu-service:blocked:missing-qemu-ssh-banner`
   - Expected: simpleos_multiconfig_live_status(missing_fpga) equals `blocked:fpga-serial:blocked:missing-fpga-uart-terminal`
   - Expected: simpleos_multiconfig_live_status(missing_renderdoc) equals `blocked:renderdoc-artifact:blocked:missing-simple-rdoc-magic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 63 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("aggregates live evidence gates before completion")
val live_status = read_multiconfig_live_contract_status()
expect(live_status).to_equal("pass")
val keys = simpleos_multiconfig_live_required_evidence_keys()
assert_true(text_list_contains_value(keys, "simpleos_qemu_service_evidence_status"))
assert_true(text_list_contains_value(keys, "simpleos_fpga_serial_evidence_status"))
assert_true(text_list_contains_value(keys, "simpleos_engine2d_vulkan_evidence_status"))
assert_true(text_list_contains_value(keys, "simpleos_renderdoc_artifact_evidence_status"))
assert_true(text_list_contains_value(keys, "simpleos_wm_structured_compare_evidence_status"))
assert_true(text_list_contains_value(keys, "simpleos_wm_renderdoc_evidence_status"))
assert_true(text_list_contains_value(keys, "simpleos_screen_evidence_status"))
for screen_key in simpleos_screen_required_evidence_keys():
    assert_true(text_list_contains_value(keys, screen_key))
expect(simpleos_screen_required_evidence_keys().len()).to_equal(28)
assert_true(text_list_contains_value(
    simpleos_screen_required_evidence_keys(),
    "simpleos_screen_2d_screendump_distinct_colors"
))

val pass_evidence = SimpleOsMulticonfigLiveEvidence(
    qemu_service_status: simpleos_qemu_service_evidence_status(passing_simpleos_qemu_service_evidence()),
    fpga_serial_status: simpleos_fpga_serial_status(passing_simpleos_fpga_serial_evidence()),
    engine2d_vulkan_status: simpleos_engine2d_vulkan_status(passing_simpleos_engine2d_vulkan_evidence()),
    renderdoc_artifact_status: simpleos_renderdoc_artifact_status(passing_simpleos_renderdoc_artifact_evidence()),
    wm_structured_compare_status: simpleos_wm_structured_compare_status(passing_simpleos_wm_structured_compare_evidence()),
    wm_renderdoc_status: simpleos_wm_renderdoc_evidence_status(passing_simpleos_wm_renderdoc_evidence()),
    screen_status: "pass"
)
expect(simpleos_multiconfig_live_status(pass_evidence)).to_equal("pass")

val missing_qemu = SimpleOsMulticonfigLiveEvidence(
    qemu_service_status: "blocked:missing-qemu-ssh-banner",
    fpga_serial_status: "pass",
    engine2d_vulkan_status: "pass",
    renderdoc_artifact_status: "pass",
    wm_structured_compare_status: "pass",
    wm_renderdoc_status: "pass",
    screen_status: "pass"
)
expect(simpleos_multiconfig_live_status(missing_qemu)).to_equal("blocked:qemu-service:blocked:missing-qemu-ssh-banner")

val missing_fpga = SimpleOsMulticonfigLiveEvidence(
    qemu_service_status: "pass",
    fpga_serial_status: "blocked:missing-fpga-uart-terminal",
    engine2d_vulkan_status: "pass",
    renderdoc_artifact_status: "pass",
    wm_structured_compare_status: "pass",
    wm_renderdoc_status: "pass",
    screen_status: "pass"
)
expect(simpleos_multiconfig_live_status(missing_fpga)).to_equal("blocked:fpga-serial:blocked:missing-fpga-uart-terminal")

val missing_renderdoc = SimpleOsMulticonfigLiveEvidence(
    qemu_service_status: "pass",
    fpga_serial_status: "pass",
    engine2d_vulkan_status: "pass",
    renderdoc_artifact_status: "blocked:missing-simple-rdoc-magic",
    wm_structured_compare_status: "pass",
    wm_renderdoc_status: "pass",
    screen_status: "pass"
)
expect(simpleos_multiconfig_live_status(missing_renderdoc)).to_equal("blocked:renderdoc-artifact:blocked:missing-simple-rdoc-magic")
```

</details>

#### reports default live evidence as blocked until artifacts are supplied

- reports default live evidence as blocked until artifacts are supplied
   - Expected: evidence.qemu_service_status equals `blocked:missing-qemu-serial-console`
   - Expected: evidence.fpga_serial_status equals `blocked:missing-fpga-uart-terminal`
   - Expected: evidence.engine2d_vulkan_status equals `blocked:missing-engine2d-vulkan-backend`
   - Expected: evidence.renderdoc_artifact_status equals `blocked:missing-renderdoc-capture-simple-mode`
   - Expected: evidence.wm_structured_compare_status equals `blocked:missing-qemu-wm-scene`
   - Expected: evidence.wm_renderdoc_status equals `blocked:missing-simple-rdoc-magic`
   - Expected: evidence.screen_status equals `missing`
   - Expected: simpleos_multiconfig_live_status(evidence) equals `blocked:qemu-service:blocked:missing-qemu-serial-console`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reports default live evidence as blocked until artifacts are supplied")
val evidence = default_blocked_simpleos_multiconfig_live_evidence()
expect(evidence.qemu_service_status).to_equal("blocked:missing-qemu-serial-console")
expect(evidence.fpga_serial_status).to_equal("blocked:missing-fpga-uart-terminal")
expect(evidence.engine2d_vulkan_status).to_equal("blocked:missing-engine2d-vulkan-backend")
expect(evidence.renderdoc_artifact_status).to_equal("blocked:missing-renderdoc-capture-simple-mode")
expect(evidence.wm_structured_compare_status).to_equal("blocked:missing-qemu-wm-scene")
expect(evidence.wm_renderdoc_status).to_equal("blocked:missing-simple-rdoc-magic")
expect(evidence.screen_status).to_equal("missing")
expect(simpleos_multiconfig_live_status(evidence)).to_equal("blocked:qemu-service:blocked:missing-qemu-serial-console")
```

</details>

#### aggregates status rows emitted by live evidence wrappers

- aggregates status rows emitted by live evidence wrappers
   - Expected: simpleos_multiconfig_live_status(pass_rows) equals `pass`
   - Expected: simpleos_multiconfig_live_status(qemu_blocked) equals `blocked:qemu-service:blocked:missing-qemu-http-200`
   - Expected: simpleos_multiconfig_live_status(wm_blocked) equals `blocked:wm-structured-compare:blocked:wm-argb-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("aggregates status rows emitted by live evidence wrappers")
val pass_rows = simpleos_multiconfig_live_evidence_from_status_rows(
    "pass",
    "pass",
    "pass",
    "pass",
    "pass",
    "pass",
    "pass"
)
expect(simpleos_multiconfig_live_status(pass_rows)).to_equal("pass")

val qemu_blocked = simpleos_multiconfig_live_evidence_from_status_rows(
    "blocked:missing-qemu-http-200",
    "pass",
    "pass",
    "pass",
    "pass",
    "pass",
    "pass"
)
expect(simpleos_multiconfig_live_status(qemu_blocked)).to_equal("blocked:qemu-service:blocked:missing-qemu-http-200")

val wm_blocked = simpleos_multiconfig_live_evidence_from_status_rows(
    "pass",
    "pass",
    "pass",
    "pass",
    "blocked:wm-argb-mismatch",
    "pass",
    "pass"
)
expect(simpleos_multiconfig_live_status(wm_blocked)).to_equal("blocked:wm-structured-compare:blocked:wm-argb-mismatch")
```

</details>

<details>
<summary>Advanced: marks the static profile matrix ready while live evidence remains required</summary>

#### marks the static profile matrix ready while live evidence remains required

- marks the static profile matrix ready while live evidence remains required
   - Expected: qemu_status equals `ready`
   - Expected: fpga_status equals `ready`
   - Expected: simpleos_multiconfig_goal_status() equals `profiles-ready-live-evidence-required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("marks the static profile matrix ready while live evidence remains required")
val qemu_status = profile_all_requirements_status(
    qemu_riscv64_desktop_profile(),
    qemu_riscv64_required_capabilities()
)
val fpga_status = profile_all_requirements_status(
    fpga_riscv64_serial_profile(),
    fpga_riscv64_allowed_capabilities()
)
expect(qemu_status).to_equal("ready")
expect(fpga_status).to_equal("ready")
expect(simpleos_multiconfig_goal_status()).to_equal("profiles-ready-live-evidence-required")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/os/simpleos_multiconfig_vulkan_wm_plan.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `12162e9cf7d6b3efeb3245ef3d975a1d2fe5c773c81cf68ce248fe670e4c9e80`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `12162e9cf7d6b3efeb3245ef3d975a1d2fe5c773c81cf68ce248fe670e4c9e80`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `12162e9cf7d6b3efeb3245ef3d975a1d2fe5c773c81cf68ce248fe670e4c9e80`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/simpleos_config_matrix_spec.spl
mirror: doc/06_spec/01_unit/os/simpleos_config_matrix_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/simpleos_config_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/simpleos_config_matrix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/simpleos_config_matrix_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/simpleos_config_matrix_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines QEMU RV64 desktop as the service GPU WM Vulkan profile' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/simpleos_config_matrix_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps FPGA RV64 serial-only and fail-closed for desktop capabilities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/simpleos_config_matrix_spec.spl:247:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes QEMU RV64 desktop launch args with service ports and GPU' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
