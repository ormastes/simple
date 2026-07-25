# SimpleOS Host Configuration Matrix

- status: fail
- fpga_serial_only_config: pass
- qemu_network_gui_config: partial-rv64-wm-missing
- qemu_riscv64_network_ports: pass
- qemu_riscv64_wm_live: missing
- qemu_simpleos_wm_live: pass
- fpga_network_capacity_config: planned
- simpleos_host_launch_config: pass
- wm_host_mode_policy: pass
- qemu_network_ports: ssh=2222->22, web/db covered by RISC-V HTTP/DBFS gate
- qemu_gui_backend: Vulkan-backed host/browser evidence plus x86_64 SimpleOS QMP MDI framebuffer evidence
- qemu_network_gui_reason: RV64 network and x86_64 SimpleOS WM are represented; RV64 live WM framebuffer is blocked by native entry-closure symbol mismatch
- qemu_riscv64_wm_reason: blocked by RV64 native entry-closure symbol mismatch before useful QEMU framebuffer evidence
- qemu_riscv64_wm_tracking: doc/08_tracking/bug/simpleos_rv64_wm_live_framebuffer_gate_2026-06-30.md
- fpga_serial_transport: UART console, telnet/ssh-compatible serial bridge harness
- fpga_network_capacity_reason: explicit future lane; not claimed as live silicon evidence
- gui_entry_latest_dir: build/tmp/gui_entry_engine2d_wm_simple_web_spec_3406515_1782861032385213
