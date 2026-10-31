# NVME/OS system specs still RED after relfix (2026-10-31)

Run on the Windows host with the Rust seed (`build/fix/seed.exe`, base of
this tree). Fixed groups are in the branch history; this lists what stays red
and why. No assertion was weakened and nothing was skipped.

## Seed bugs (src/compiler_rust, not edited)

1. `mut buf: [u8]` mutation not visible to the caller under `seed test`
   (works under `seed run`). Repro: `build/fix/repro/mutbuf_spec.spl`
   (`expect(out).to_equal([7u8, 7u8])` sees `[0, 0]`). Explains
   `os/feature/vfs_exec_bytes_spec.spl` ("keeps NVFS path reads pure Simple").
2. `file_write` returns `true` but writes nothing inside a spec `it` body
   (works under `seed run`). Repro: `build/fix/repro/fw_spec.spl`. Blocks
   `nvme_firmware/nvme_nand_capture_spec.spl` after the missing
   `capture_text` helper was added to the spec.
3. `UiAccessStore.memory()?` returns Err in a spec (embedded SQL backing not
   available in the seed): `os/feature/ui_access_protocol_spec.spl`
   REQ-UAP-018/019 ("try: early return"). 6 of 8 examples now pass.

## Slow, not wrong (need more than the 120 s per-spec budget on the seed)

`nvme_gen_{get_log_error,get_log_smart,nvm_read,nvm_write,status_code_reporting}`,
`nvme_emu_fault_recovery`, `nvme_emu_media_slice_b`, `nvme_firmware_simulation`,
`hw_ir_duplicate_literal_ratchet_gate`: the inner program
(`nvme_emu_recovery_check.spl`) prints `NVME EMU RECOVERY OK` rc=0 but needs
about 10 minutes interpreted. `nvme_gen_admin_queue_pair` timed out once under
host load (it is a 5 s spec on an idle host). No `@timeout_secs` added.

## ENV-BLOCKED

- GHDL absent (`which ghdl`): `riscv_gen2_hwir_foundation` (46 of 56),
  `riscv_gen2_scalar_i_product_cycle`, `riscv_gen2_scalar_alu_projection`.
- QEMU/board/media or self-hosted compiler required: `nvme_rv32_{smp_boot,fpga_boot,minimal_live}`,
  `rv32_nvme_host_axi_mmio`, `rv32_nvme_nand_read_level` ("rv32-nvme compiler is the
  Rust bootstrap seed"), `simpleos_riscv_smf_fs_launch`,
  `simpleos_compiler_filesystem_qemu_checker`, `nvme_emulator_seam` (Lean),
  `nvme_cosmos_*_coverage`, `nvme_baremetal_wrapper_coverage` (coverage tools).
- `riscv32_riscv64_fpga_simpleos_production`: 6 intentionally failing
  "implement ..." placeholders.

## Product source absent from this tree (spec ahead of release/1.0)

- 51 files under `src/compiler/50.mir/hwir/` exist at `a8244005f9b` (not an
  ancestor) but not here, e.g. `riscv_scalar_decoder.spl`,
  `riscv_scalar_runtime_pipeline_v*`: specs `riscv_gen2_scalar_decoder`,
  `riscv_gen2_runtime_pipeline_v6..v9_*` fail with
  `Module "compiler.mir.hwir" does not export ...`.
- `nvme_firmware_remaining_gates`: `openssd_config.spl` lacks
  `TARGET_RV32_QEMU_RAM_NAND`, `TARGET_RV32_KV260_AXI_RAM_NAND`,
  `TARGET_INVALID`, `invalid_target_config()` and the `available` field
  (spec also wants unknown targets to fail closed, which changes
  `nvme_fw_target_config(99)`; a design decision).
- Source-text contract specs in `simpleos_gpu_host/*` (`HOST_GPU_DAEMON_VULKAN_SHUTDOWN`,
  `processing_ir_fault_reason` helper imports, fallback receipt validators, ...)
  assert snippets that the product files do not contain.
- `typed_address_algebra_ratchet_gate`: 238 bare-i64 address params vs baseline
  202; needs a reviewed baseline update or the regression fixed.
- `hardware/feature/{riscv_fpga_linux,riscv_linux_rtl_dual_arch_completion,rv64_linux_rtl_pipeline}`:
  `hardware.*` module paths resolve to `src/lib/hardware/...`; unresolved on the
  seed. `simpleos_proton_substrate`, `tmux_simpleos`, `x86_64_desktop_driver_completion`,
  `gpu_backend_failure_injection`, `processing_ir_offload_break_even`,
  `macos_metal_processing_ir_failure_injection`: not triaged to a cause.
