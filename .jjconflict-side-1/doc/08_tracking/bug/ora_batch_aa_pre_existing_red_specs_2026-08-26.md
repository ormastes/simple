# ora_batch_aa specs RED at pre-edit baseline (sspec modernization batch)

- Date: 2026-08-26
- Discovered during: sspec-maintain modernization of `/tmp/sspec_census/ora_batch_aa`
- Status: OPEN (one entry per spec; baseline proven by restoring the pre-edit
  working-copy content and re-running `bin/simple test <spec>`)

Each spec below failed at its pre-edit baseline BEFORE any modernization edit.
Where the modernized version still fails, the failing assertion is identical
to the baseline's. Structural modernization was still applied (scores in
`/tmp/sspec_aa/pipeline.log`).

## Entries

- `test/01_unit/os/dma_driver_spec.spl` — baseline `Results: 1 total, 0 passed, 1 failed`
  (no executable scenario bodies; model classes only, no assertions).
- `test/01_unit/os/scheduler_isolation_spec.spl` — same shape, `1 total, 0 passed, 1 failed`.
- `test/03_system/app/simple_2d/feature/legacy_web_gui_wm_font_route_spec.spl` — `2 total, 1 passed, 1 failed`.
- `test/01_unit/app/mcp_unit/fileio_protection_spec.spl` — `27 total, 24 passed, 3 failed`.
- `test/03_system/app/compiler/feature/host_cpu_runtime_variants_spec.spl` — `11 total, 10 passed, 1 failed`
  (modernized to score 100; still red at the same baseline assertion).
- `test/03_system/gpu/metal_backend_mac_host_spec.spl` — `6 total, 3 passed, 3 failed, 1 skipped`
  (mac-host Metal lane; likely requires macOS host).
- `test/03_system/app/lib/feature/common_compression_framework_spec.spl` — `1 total, 0 passed, 1 failed`.
- `test/03_system/compiler/rtl_mdsoc_byte_equal_spec.spl` — `12 total, 8 passed, 4 failed, 3 skipped`.
- `test/unit/lib/std/ml/tracking/run_spec.spl` — `1 total, 0 passed, 1 failed` (pending scaffold, no assertions).
- `test/03_system/os/vulkan/board_vulkan_img_bxe_submit_readback_system_spec.spl` — `1 total, 0 passed, 1 failed, 1 skipped`
  (board lane; QEMU/board evidence required).
- `test/01_unit/lib/nogc_sync_mut/js/engine/js_vm_reclamation_spec.spl` — `4 total, 0 passed, 4 failed`.

- `test/03_system/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.spl` — `2 total, 1 passed, 1 failed`.

- `test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl` — `3 total, 0 passed, 3 failed`.

- `test/system/os_network_spec.spl` — `1 total, 0 passed, 1 failed`.

- `test/01_unit/lib/std/parser/error_recovery_spec.spl` — `1 total, 0 passed, 1 failed`.

- `test/03_system/app/simpleos/feature/tmux_simpleos_spec.spl` — `14 total, 3 passed, 11 failed`.

- `test/02_integration/os/port/make_os_disk_fat32_integrity_spec.spl` — `3 total, 2 passed, 1 failed`.

- `test/system/t32_tools/qemu_manual_spec.spl` — `1 total, 0 passed, 1 failed`.

- `test/03_system/app/spipe/feature/spipe_knowledge_compiler_refactor_spec.spl` — `3 total, 0 passed, 3 failed`.

- `test/02_integration/storage/dbfs/nvfs_hosted_no_regression_spec.spl` — `5 total, 2 passed, 3 failed`.

- `test/system/app/compiler/feature/all_regions_spec.spl` — `1 total, 0 passed, 1 failed`.

- `test/01_unit/compiler/hir/bootstrap_expr_args_source_spec.spl` — `1 total, 0 passed, 1 failed`.

- `test/unit/app/test_runner/driver_spec.spl` — `1 total, 0 passed, 1 failed`.

- `test/03_system/check/simpleos_arm64_evidence_tooling_spec.spl` — `1 total, 0 passed, 1 failed`.

- `test/01_unit/os/kernel/arch/syscall_dispatch_spec.spl` — `11 total, 0 passed, 11 failed`.

- `test/02_integration/rendering/winit_ordered_committed_text_spec.spl` — `3 total, 2 passed, 1 failed`.

- `test/03_system/os/wm/simple_wm_render_provenance_spec.spl` — `5 total, 0 passed, 5 failed`.

- `test/03_system/os/qemu/windows_sosix_qemu_matrix_runner_spec.spl` — `3 total, 2 passed, 1 failed`.

- `test/unit/compiler/common/config_spec.spl` — `1 total, 0 passed, 1 failed`.

- `test/system/app/simpleos/feature/simpleos_proton_substrate_spec.spl` — `1 total, 0 passed, 1 failed`.

- `test/01_unit/app/test_runner/quickcheck_spec.spl` — `93 total, 61 passed, 32 failed`.

- `test/01_unit/os/qemu_runner_tool_validator_spec.spl` — `1 total, 0 passed, 1 failed`.

- `test/03_system/feature/compiler/x86_avx2_custom_native_execution_spec.spl` — `1 total, 0 passed, 1 failed, 1 skipped`.

- `test/01_unit/os/services/vfs/.spipe_wrapped_entry_vfs_boot_nvme_lease_spec.spl` — `13 total, 9 passed, 4 failed`.

- `test/03_system/feature/usage/actors_spec.spl` — `1 total, 0 passed, 1 failed`.

- `test/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.spl` — `5 total, 0 passed, 5 failed`.

- `test/03_system/app/ui/feature/backend_isolation_gate_spec.spl` — `9 total, 8 passed, 1 failed`.

- `test/system/app/tooling/feature/warning_allow_root_cause_cleanup_spec.spl` — `1 total, 0 passed, 1 failed`.

(This record is appended as the batch progresses; see also
`wine_vm_write_readback_token_renamed_specs_red_2026-08-26.md` for the Wine
evidence-token family.)
