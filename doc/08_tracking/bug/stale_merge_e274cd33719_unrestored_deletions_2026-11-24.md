# Stale merge e274cd33719: deletions still missing on release/1.0.0

- **Date:** 2026-11-24
- **Audited tip:** `fe0dc538937` (origin/release/1.0.0)
- **Culprit:** `e274cd33719` "chore: merge all share-history worktree branches into main" (single parent `0fce018eda3`)
- **Class:** stale-snapshot rewind, see `doc/07_guide/infra/vcs/stale_merge_snapshot_rewind.md`
- **Method:** static only. No runnable `simple` binary and no build was used; nothing here was compiled or executed.

## Method

1. Files deleted: `git diff --diff-filter=D 0fce018eda3 e274cd33719`.
2. For every modified `.spl/.shs/.rs/.c/.h` under `src/` and `scripts/` (vendor excluded), the set of
   column-0 definitions (`fn/struct/class/enum/trait/val/var/const/extern fn/...`) at the parent minus the
   set at the merge result.
3. Each removed (path, name) was looked up at the audited tip: defined at the same path, defined at column 0
   anywhere under `src/`/`scripts/`, or referenced by name in `src test scripts .github examples`.
4. A candidate was restored only when: the definition line was never re-added after e274 on that path
   (`git log -G`), a live importer or same-file caller exists, and every identifier the restored body
   calls is still present in the target file.

## Counts

| class | count |
|---|---|
| files deleted by e274 | 30 |
| - back at the audited tip (RESTORED) | 6 |
| - still absent, unreferenced (generated tauri/cargo artifacts, logs, scratch examples, one spec, one bug doc) | 23 |
| - still absent, referenced | 1 (`test/02_integration/compiler/cache_v2/fixtures/corrupt_blob.bin`, named only by the sibling `FILE.md`; `*.bin` is gitignored, not restored) |
| column-0 definitions removed (in 1712 files) | 9148 |
| - defined again at the same path (RESTORED) | 7507 |
| - same name defined at column 0 elsewhere (moved or homonym) | 548 |
| - defined nowhere at column 0 | 1093 rows / 1021 names |
| -- names with no reference at all (GONE-AND-UNREFERENCED) | 707 |
| -- names now defined as a nested/indented or test-local definition | 101 |
| -- names referenced in comments only | 12 |
| -- names with a dangling code reference | 201 |
| MISSING-BUT-REFERENCED `.spl` candidates analysed (dangling names plus explicit imports of a name gone from its module) | 179 |
| - restored by this change | 45 |
| - not restored: body depends on identifiers no longer in the file | 27 |
| - not restored: referenced by name only, no importer of the module found | 20 |
| - not restored: definition line touched by a later commit after e274 (intent unverified); still referenced | 86 |
| - not restored: file no longer exists | 1 |
| MISSING-BUT-REFERENCED `.c/.h` names (not verified, C definition regex is coarse) | 46 |

Also restored: `src/app/portal/public/css/app.css` (e274 cut 182 lines, the git-browser styles
`.repo-header .repo-subnav .repo-table .file-tree .code-view .diff-* .readme .breadcrumb .error-page
.submodule-entry .sha`; all still emitted by `src/app/portal/git_views.spl`; no commit touched the file since).

Adaptations to the restored text: `nil` written as `None` (push-nil-outside-unsafe-added gate); blocks are
appended at the end of their file; an `export` line is re-added where the parent exported the name.

## Restored (45 definitions)

| file | name |
|---|---|
| `src/app/compile/llvm_direct.spl` | `llvm_direct_minimal_c_source` |
| `src/app/office/slides/slide.spl` | `set_slide_notes` |
| `src/app/office/slides/slide.spl` | `set_slide_transition` |
| `src/app/watch/deps.spl` | `normalize_dep_file_path` |
| `src/app/wm_compare/backend_measurement_report.spl` | `backend_comparison_artifact_total_us` |
| `src/os/apps/sshd/ssh_channel.spl` | `SSH_INVALID_CHANNEL_ID` |
| `src/os/apps/sshd/ssh_channel.spl` | `SSH_MAX_CHANNELS_PER_SESSION` |
| `src/os/apps/sshd/ssh_kex_primitives.spl` | `host_key_set_has_any_algorithm` |
| `src/os/apps/sshd/ssh_session_helpers.spl` | `ssh_session_u8_at` |
| `src/os/compositor/shared_mdi_setup.spl` | `shared_mdi_surface_app_id` |
| `src/os/compositor/shared_mdi_setup.spl` | `shared_mdi_surface_content` |
| `src/os/compositor/shared_mdi_setup.spl` | `shared_mdi_surface_count` |
| `src/os/compositor/shared_mdi_setup.spl` | `shared_mdi_surface_height` |
| `src/os/compositor/shared_mdi_setup.spl` | `shared_mdi_surface_process_id` |
| `src/os/compositor/shared_mdi_setup.spl` | `shared_mdi_surface_title` |
| `src/os/compositor/shared_mdi_setup.spl` | `shared_mdi_surface_width` |
| `src/os/compositor/shared_mdi_setup.spl` | `shared_mdi_surface_x` |
| `src/os/compositor/shared_mdi_setup.spl` | `shared_mdi_surface_y` |
| `src/os/drivers/usb/xhci_regs.spl` | `XHCI_CAP_CAPLENGTH` |
| `src/os/drivers/usb/xhci_regs.spl` | `XHCI_CAP_DBOFF` |
| `src/os/drivers/usb/xhci_regs.spl` | `XHCI_CAP_HCSPARAMS1` |
| `src/os/drivers/usb/xhci_regs.spl` | `XHCI_CAP_RTSOFF` |
| `src/os/drivers/usb/xhci_regs.spl` | `XHCI_OP_CONFIG` |
| `src/os/drivers/usb/xhci_regs.spl` | `XHCI_OP_CRCR` |
| `src/os/drivers/usb/xhci_regs.spl` | `XHCI_OP_DCBAAP` |
| `src/os/drivers/usb/xhci_regs.spl` | `XHCI_OP_USBCMD` |
| `src/os/drivers/usb/xhci_regs.spl` | `XHCI_OP_USBSTS` |
| `src/os/gui/shortcut.spl` | `SC_4` |
| `src/os/gui/shortcut.spl` | `SC_9` |
| `src/os/kernel/arch/arm/pl011_common.spl` | `pl011_read_char` |
| `src/os/kernel/arch/arm32/cpu.spl` | `arm32_current_mpidr_v1` |
| `src/os/kernel/ipc/cspace_spawn.spl` | `SingleUseLedger` |
| `src/os/kernel/ipc/cspace_spawn.spl` | `atten_single_use` |
| `src/os/kernel/ipc/cspace_spawn.spl` | `spawn_with_cspace_tracked` |
| `src/os/kernel/ipc/host_gpu_ivshmem_map.spl` | `map_qemu_audio_ivshmem_bar2` |
| `src/os/kernel/ipc/host_gpu_ivshmem_map.spl` | `qemu_audio_ivshmem_window_base` |
| `src/os/kernel/ipc/message_buffer.spl` | `InlineChannel` |
| `src/os/lib/gpu_bridge/host_gpu_ivshmem.spl` | `HOST_GPU_IVSHMEM_MAX_TIMEOUT_POLLS` |
| `src/os/lib/gpu_bridge/host_gpu_ivshmem.spl` | `_host_gpu_submit_draw_ir_common` |
| `src/os/services/ds_service.spl` | `ds_notify_count_value` |
| `src/os/services/evidence/signature_codec.spl` | `simpleos_evidence_public_key_hex_decode` |
| `src/os/sosix/process.spl` | `sosix_string_vector_table_offset` |
| `src/os/userlib/net.spl` | `_NET_SEND_RANGE_CHUNK_BYTES` |
| `src/os/userlib/net.spl` | `socket_send_range` |
| `src/os/userlib/net.spl` | `socket_send_range_chunk` |

## Not restored: body dependencies missing (27)

Restoring these needs the listed identifiers back first.

| file | name | missing in file | example importer |
|---|---|---|---|
| `src/app/model3d/main.spl` | `node_world_positions` | NodeWorldPos,Pure, | test/_probe_root_tmp/probe_spec.spl |
| `src/app/office/sheets/number_format.spl` | `format_text_with_code` | no_color,text_value, | test/01_unit/app/office/sheets/number_format_spec.spl |
| `src/app/office/slides/slide.spl` | `create_slide_from_layout_id` | default_text,extension_host_ensure_command_activated,layout_registry,section_header,sectio... | test/01_unit/lib/editor/office_readers_activate_before_read_spec.spl |
| `src/app/wm_compare/backend_measurement_report.spl` | `backend_comparison_offload_efficiency_verdict` | backend_comparison_offload_overhead_verdict,backend_comparison_speed_verdict,scalar_p50_fr... | test/03_system/gui/wm_compare/backend_measurement_report_spec.spl |
| `src/app/wm_compare/backend_measurement_report.spl` | `backend_comparison_offload_overhead_verdict` | artifact_total,backend_comparison_artifact_total_us, | test/03_system/gui/wm_compare/backend_measurement_report_spec.spl |
| `src/app/wm_compare/backend_measurement_report.spl` | `backend_comparison_speed_verdict` | scalar_p50_frame_us, | test/03_system/gui/wm_compare/backend_measurement_report_spec.spl |
| `src/os/apps/sshd/ssh_auth.spl` | `ssh_check_public_key_auth` | session_id, | src/os/apps/sshd/ssh_session.spl |
| `src/os/apps/sshd/ssh_channel.spl` | `ChannelTerminalRequestV1` | None,Shell, | test/01_unit/os/apps/sshd/ssh_channel_request_authority_spec.spl |
| `src/os/apps/sshd/ssh_session_helpers.spl` | `ssh_pre_auth_control_budget_allows` | SSH_PREAUTH_CONTROL_PACKET_BUDGET,SSH_PREAUTH_REKEY_BUDGET, | src/os/apps/sshd/ssh_session_auth.spl |
| `src/os/drivers/audio/hda_controller.spl` | `hda_ack_irq_at` | HDA_REG_INTSTS,mmio_read32,mmio_write32, | src/os/services/audio/audio_service.spl |
| `src/os/drivers/audio/hda_controller.spl` | `hda_output_stream_id_at` | HDA_REG_GCAP,mmio_read16,to_i64, | src/os/services/audio/audio_service.spl |
| `src/os/drivers/audio/hda_controller.spl` | `hda_stop_stream_at` | HDA_REG_INTCTL,HDA_SD0_BASE,HDA_SD_CTL,HDA_SD_STRIDE,mmio_read32,mmio_write32,to_u32, | src/os/services/audio/audio_service.spl |
| `src/os/kernel/arch/arm/pl011_common.spl` | `pl011_data_ready` | PL011_FR_RXFE, | test/01_unit/os/arm64_desktop_arch_facade_spec.spl |
| `src/os/kernel/arch/arm64/console.spl` | `uart_data_ready` | pl011_data_ready, | examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl |
| `src/os/kernel/arch/arm64/console.spl` | `uart_read_char` | pl011_read_char, | examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl |
| `src/os/kernel/arch/arm64/ramfb.spl` | `arm64_ramfb_scanout_checksum` | simpleos_host_gpu_readback_checksum_finalize,simpleos_host_gpu_readback_checksum_step, | examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl |
| `src/os/kernel/arch/riscv64/shell_lite.spl` | `rv64_shell_format_dir_entries` | DirEntry,g_vfs_readdir, | src/os/kernel/arch/riscv64/console.spl |
| `src/os/kernel/boot/limine_boot.spl` | `limine_framebuffer_fields_valid` | LIMINE_FB_BPP_24,LIMINE_FB_BPP_32,LIMINE_FB_MAX_DIM,LIMINE_FB_MIN_DIM, | test/01_unit/os/kernel/boot/limine_boot_spec.spl |
| `src/os/services/clock_service.spl` | `clock_notify_count_value` | clock_notify_count, | test/01_unit/os/services/clock_service_spec.spl |
| `src/os/services/nvfs/core/reflink.spl` | `reflink_replace_arena` | CoW,Move,namespace_refs,new_arena,old_arena,replace_arena, | src/os/services/nvfs/posix/fs_driver_impl.spl |
| `src/os/services/sched_service.spl` | `sched_set_priority_count_value` | sched_set_priority_count, | test/01_unit/os/services/sched_service_spec.spl |
| `src/os/services/tty_service.spl` | `InputBuf` | Every,Real,pty_master_write,tty_read_input, | test/01_unit/os/tty/pty_roundtrip_spec.spl |
| `src/os/services/tty_service.spl` | `OutputBuf` | Real,tty_read_output, | test/01_unit/os/tty/tty_write_delivery_spec.spl |
| `src/os/services/tty_service.spl` | `tty_service_manifest` | ServiceManifest,max_restarts,restart_policy,service_v1, | test/01_unit/os/services/service_manifest_integration_spec.spl |
| `src/app/llm_caret/claude_full/hooks/useTasksV2.spl` | `TasksV2HookEnvironment` | - | test/03_system/tools/llm/claude_full/hooks/useTasksV2_spec.spl |
| `src/app/llm_caret/claude_full/query.spl` | `BudgetTracker` | - | test/03_system/tools/llm/claude_full/query_spec.spl |
| `src/app/wm_compare/backend_measurement_report.spl` | `backend_comparison_scalar_p50_us` | - | test/03_system/gui/wm_compare/backend_measurement_report_spec.spl |

## Not restored: no importer of the module found (20)

| file | name |
|---|---|
| `src/app/jj/sync.spl` | `current_work_bookmark` |
| `src/os/drivers/usb/xhci_driver.spl` | `xhci_wait_for_event_type` |
| `src/os/kernel/boot/mmio.spl` | `mmio_invalidate_tlb` |
| `src/os/kernel/boot/riscv_services.spl` | `_sffi_log_raw_println` |
| `src/os/kernel/boot/riscv_services.spl` | `_sffi_net_init` |
| `src/os/kernel/boot/riscv_services.spl` | `_sffi_net_rx_ready` |
| `src/os/kernel/boot/riscv_services.spl` | `_sffi_net_stats` |
| `src/os/kernel/boot/riscv_services.spl` | `_sffi_net_tx_test` |
| `src/os/kernel/boot/riscv_services.spl` | `_sffi_pci_device_count` |
| `src/os/kernel/boot/riscv_services.spl` | `_sffi_pci_get_field` |
| `src/os/kernel/boot/riscv_services.spl` | `_sffi_storage_capacity_sectors` |
| `src/os/kernel/boot/riscv_services.spl` | `_sffi_storage_init` |
| `src/os/kernel/boot/riscv_services.spl` | `_sffi_storage_nvfs_arena_ready` |
| `src/os/kernel/boot/riscv_services.spl` | `_sffi_storage_nvfs_ready` |
| `src/os/kernel/boot/riscv_services.spl` | `_sffi_storage_read_probe` |
| `src/app/gui_perf/smf_dynlib_artifact.spl` | `gui_smf_artifact_contract_with_sha256` |
| `src/os/drivers/nvme/nvme_storage_model.spl` | `nvme_namespace_mode_is_system` |
| `src/os/drivers/usb/xhci_trb.spl` | `TRB_TRT_IN_DATA` |
| `src/os/kernel/memory/user_address_space.spl` | `ARM64_FS_EXEC_FRAME_BASE` |
| `src/os/lib/gpu_bridge/host_gpu_ivshmem.spl` | `HOST_GPU_IVSHMEM_REQUEST_BUDGET_US` |

## Not restored: definition line touched by a later commit (86)

The name is still referenced and still undefined. `git log -G` reports a post-e274 commit on its definition line (possibly a side branch merged later), so the absence is not
attributable to e274 alone. Each needs an owner decision.

| file | name |
|---|---|
| `src/app/gen_cache_model/main.spl` | `g_seq` |
| `src/app/interpreter/async_runtime/mailbox.spl` | `MailboxConfig__bounded` |
| `src/app/interpreter/async_runtime/mailbox.spl` | `MailboxConfig__default` |
| `src/app/interpreter/async_runtime/mailbox.spl` | `MailboxConfig__unlimited` |
| `src/app/interpreter/async_runtime/mailbox.spl` | `MailboxConfig__with_priority` |
| `src/app/interpreter/async_runtime/mailbox.spl` | `MailboxStats__new` |
| `src/app/interpreter/async_runtime/mailbox.spl` | `Mailbox__default` |
| `src/app/interpreter/async_runtime/mailbox.spl` | `Mailbox__new` |
| `src/app/io/cli_ops.spl` | `cli_run_tests_process_args` |
| `src/app/mcp/cli_passthrough.spl` | `_cli_positional_error` |
| `src/app/ui_shared_mdi/main.spl` | `mdi_env_get` |
| `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl` | `_sffi_transient_heap_promote` |
| `src/compiler/10.frontend/core/_Ast/decl_nodes.spl` | `_sffi_env_remove_required` |
| `src/compiler/10.frontend/core/_Ast/decl_nodes.spl` | `_sffi_env_set_required` |
| `src/compiler/10.frontend/core/parser.spl` | `par_col_slot` |
| `src/compiler/10.frontend/core/parser.spl` | `par_line_slot` |
| `src/compiler/10.frontend/core/parser.spl` | `par_text_slot` |
| `src/compiler/10.frontend/core/parser_preprocessor.spl` | `_pp_pos` |
| `src/compiler/10.frontend/core/parser_preprocessor.spl` | `_pp_tokens` |
| `src/compiler/20.hir/hir_lowering/_Items/lowering_helpers.spl` | `_sffi_transient_heap_promote` |
| `src/compiler/60.mir_opt/mir_opt/pattern/rules_crypto.spl` | `SYM_OS_CRC32_UPDATE_BYTE` |
| `src/compiler/60.mir_opt/mir_opt/pattern/rules_crypto.spl` | `SYM_OS_CRC32_UPDATE_U32` |
| `src/compiler/60.mir_opt/mir_opt/pattern/rules_crypto.spl` | `SYM_OS_CRC32_UPDATE_U64` |
| `src/compiler/80.driver/driver_api_types.spl` | `_driver_api_runtime_env_raw` |
| `src/compiler/90.tools/duplicate_check/semantic.spl` | `semantic_bucket_accepts_member` |
| `src/compiler/99.loader/loader/smf_mmap_native.spl` | `_sffi_ptr_write_i32` |
| `src/compiler/99.loader/loader/smf_mmap_native.spl` | `_sffi_ptr_write_i64` |
| `src/compiler/99.loader/loader/smf_mmap_native.spl` | `_sffi_ptr_write_u8` |
| `src/lib/common/js/engine/runtime.spl` | `js_runtime_with_default_logger` |
| `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl` | `_run_scoped_child` |
| `src/lib/nogc_sync_mut/test_runner/test_runner_output.spl` | `test_group_summaries_json` |
| `src/lib/scv/maintenance.spl` | `scv_gc_roots_reachable` |
| `src/os/_QemuRunner/os_build_run.spl` | `_is_host_gpu_probe_target` |
| `src/os/apps/dbd/dbd_protocol.spl` | `DbdTransactionOwnerV1` |
| `src/os/apps/dbd/dbd_protocol.spl` | `DbdTransactionQueueStatusV1` |
| `src/os/apps/dbd/dbd_protocol.spl` | `dbd_command_has_durable_journal_semantics` |
| `src/os/apps/dbd/dbd_protocol.spl` | `dbd_command_terminates_session` |
| `src/os/compositor/host_wm_theme_bootstrap.spl` | `install_host_wm_theme` |
| `src/os/crypto/poly1305.spl` | `poly1305_key_gen` |
| `src/os/crypto/sha256.spl` | `sha256_hmac_from_list` |
| `src/os/crypto/sha256.spl` | `sha256_stream_finish` |
| `src/os/crypto/sha256.spl` | `sha256_stream_new` |
| `src/os/crypto/sha256.spl` | `sha256_stream_update` |
| `src/os/drivers/virtio/virtio_gpu_ops.spl` | `GPU_RECOVERY_MAX_ATTEMPTS` |
| `src/os/drivers/virtio/virtio_gpu_ops.spl` | `GpuErrorKind` |
| `src/os/drivers/virtio/virtio_gpu_ops.spl` | `GpuOpOutcome` |
| `src/os/drivers/virtio/virtio_gpu_ops.spl` | `RecoveryStep` |
| `src/os/drivers/virtio/virtio_gpu_ops.spl` | `virtio_gpu_cmd_get_display_info_with_recovery` |
| `src/os/drivers/virtio/virtio_gpu_ops.spl` | `virtio_gpu_cmd_set_scanout_with_recovery` |
| `src/os/drivers/virtio/virtio_gpu_ops.spl` | `virtio_gpu_recovery_next_step` |
| `src/os/drivers/virtio/virtio_gpu_ops.spl` | `virtio_gpu_recovery_run` |
| `src/os/kernel/arch/riscv64/display.spl` | `riscv64_display_generation` |
| `src/os/kernel/arch/riscv64/hal_smp.spl` | `hal_smp_hsm_target` |
| `src/os/kernel/arch/riscv64/hal_smp.spl` | `hal_smp_ipi_window` |
| `src/os/kernel/loader/stack_builder.spl` | `build_initial_stack` |
| `src/os/kernel/memory/memory_leveling_vmm.spl` | `memory_vmm_prepare_swap_in` |
| `src/os/kernel/memory/pmm.spl` | `pmm_put_page` |
| `src/os/kernel/memory/vmm_core.spl` | `VMM_VMA_SHARED_FILE` |
| `src/os/kernel/memory/vmm_core.spl` | `vmm_active_root` |
| `src/os/kernel/memory/vmm_core.spl` | `vmm_map_page_pte_bits` |
| `src/os/kernel/memory/vmm_vma.spl` | `VmmCowCloneResult` |
| `src/os/kernel/memory/vmm_vma.spl` | `vmm_handle_shared_file_fault` |
| `src/os/kernel/net/rt_net_socket_facade.spl` | `RT_NET_SOCKET_READ_MAX` |
| `src/os/kernel/net/rt_net_socket_facade.spl` | `_rt_net_exact_write_result` |
| `src/os/kernel/net/rt_net_socket_facade.spl` | `rt_net_bind_and_listen` |
| `src/os/kernel/net/rt_net_socket_facade.spl` | `rt_net_last_ssh_plain_payload_len` |
| `src/os/kernel/types/device_mem_types.spl` | `pci_bdf_pack` |
| `src/os/port/_BootstrapCross/cross_compile_stages.spl` | `host_seed_identity_matches` |
| `src/os/port/llvm/build.spl` | `_cross_supported_targets` |
| `src/os/qemu_runner_part2.spl` | `_qemu_env_get` |
| `src/os/qemu_runner_part2.spl` | `_qemu_env_set` |
| `src/os/qemu_runner_part2.spl` | `_qemu_file_delete` |
| `src/os/qemu_runner_part2.spl` | `_qemu_file_read_text` |
| `src/os/qemu_runner_part2.spl` | `_qemu_file_write_text` |
| `src/os/qemu_systest_contract.spl` | `riscv64_desktop_qemu_args` |
| `src/os/qemu_systest_contract.spl` | `riscv64_desktop_qemu_args_status` |
| `src/os/services/wm/wm_host_2d_simpleos.spl` | `ps2_event_source_init` |
| `src/os/sosix/fs/ipc_codec_v1.spl` | `SOSIX_FS_IPC_MAX_REGISTERED_BUFFER_BYTES_V1` |
| `src/os/tls13/handshake13.spl` | `GROUP_X25519_MLKEM768` |
| `src/os/tls13/handshake13.spl` | `HYBRID_CLIENT_SHARE_BYTES` |
| `src/os/tls13/handshake13.spl` | `HYBRID_SERVER_SHARE_BYTES` |
| `src/os/tls13/handshake13_ext_builders.spl` | `build_client_hello_bytes_with_x25519_mlkem768` |
| `src/os/tls13/handshake13_hrr.spl` | `build_client_hello2_bytes_with_x25519_mlkem768` |
| `src/os/tls13/handshake13_hrr.spl` | `process_hrr_after_serverhello_with_x25519_mlkem768` |
| `src/os/tls13/server.spl` | `tls13_server_entropy_admits` |
| `src/os/tls13/server_builders.spl` | `build_certificate_verify_checked` |

## Not verified: C/H names with dangling references (46)

| file | name |
|---|---|
| `src/os/kernel/arch/arm32/cosmos/cosmos_ftl.c` | `crc32_u32` |
| `src/os/kernel/arch/arm32/cosmos/cosmos_pcie.c` | `cosmos_pcie_host_dma_counter_index` |
| `src/os/kernel/arch/arm32/cosmos/cosmos_pcie.c` | `cosmos_pcie_host_dma_counter_shift` |
| `src/os/kernel/arch/arm32/cosmos/cosmos_pcie.c` | `cosmos_pcie_host_dma_device_buffer_valid` |
| `src/os/kernel/arch/arm32/cosmos/cosmos_pcie.c` | `cosmos_pcie_host_dma_direct_valid` |
| `src/os/kernel/arch/arm32/cosmos/cosmos_pcie.c` | `cosmos_pcie_nvme_cmd_word_valid` |
| `src/os/kernel/arch/arm32/cosmos/cosmos_pcie.c` | `cosmos_pcie_snapshot_status` |
| `src/os/kernel/arch/arm32/cosmos/cosmos_pcie.c` | `cosmos_pcie_snapshots_equal` |
| `src/os/kernel/arch/arm32/cosmos/cosmos_uart.c` | `cosmos_exception_halt` |
| `src/os/kernel/arch/arm32/cosmos/cosmos_uart.c` | `cosmos_report_status` |
| `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` | `rt_riscv64_virtio_input_start_modern` |
| `src/os/libc/include/string.h` | `wmemcmp` |
| `src/os/libc/include/wchar.h` | `mbsrtowcs` |
| `src/os/libc/include/wchar.h` | `swprintf` |
| `src/os/libc/include/wchar.h` | `wcsrchr` |
| `src/os/libc/include/wchar.h` | `wcsstr` |
| `src/os/libc/include/wchar.h` | `wcstoull` |
| `src/os/libc/include/wchar.h` | `wcsxfrm_l` |
| `src/os/libc/simpleos_cxxabi.c` | `_ZdlPvmSt11align_val_t` |
| `src/os/libc/simpleos_cxxabi.c` | `__cxa_thread_atexit` |
| `src/os/libc/simpleos_cxxabi.c` | `linux_syscall1` |
| `src/os/libc/simpleos_cxxabi.c` | `running_on_linux_host` |
| `src/os/libc/simpleos_dlmalloc.c` | `_linux_host_mmap_pages` |
| `src/os/libc/simpleos_fork.c` | `linux_syscall0` |
| `src/os/libc/simpleos_fork.c` | `linux_syscall3` |
| `src/os/libc/simpleos_fork.c` | `linux_syscall4` |
| `src/os/libc/simpleos_fork.c` | `running_on_linux_host` |
| `src/os/libc/simpleos_fs.c` | `linux_host_stat_syscall` |
| `src/os/libc/simpleos_fs.c` | `linux_syscall2` |
| `src/os/libc/simpleos_fs.c` | `linux_syscall3` |
| `src/os/libc/simpleos_fs.c` | `running_on_linux_host` |
| `src/os/libc/simpleos_ipc.c` | `linux_syscall1` |
| `src/os/libc/simpleos_ipc.c` | `linux_syscall2` |
| `src/os/libc/simpleos_ipc.c` | `running_on_linux_host` |
| `src/os/libc/simpleos_libc.c` | `linux_syscall3` |
| `src/os/libc/simpleos_libc.c` | `linux_syscall6` |
| `src/os/libc/simpleos_libc.c` | `running_on_linux_host` |
| `src/os/libc/simpleos_libc_ext.c` | `mbsrtowcs` |
| `src/os/libc/simpleos_libc_ext.c` | `swprintf` |
| `src/os/libc/simpleos_libc_ext.c` | `wcsrchr` |
| `src/os/libc/simpleos_libc_ext.c` | `wcsstr` |
| `src/os/libc/simpleos_libc_ext.c` | `wcstoull` |
| `src/os/libc/simpleos_libc_ext.c` | `wcsxfrm_l` |
| `src/os/libc/simpleos_socket.c` | `linux_syscall6` |
| `src/os/libc/simpleos_socket.c` | `running_on_linux_host` |
| `src/os/libc/simpleos_string_ext.c` | `wmemcmp` |

## File no longer exists

- `src/compiler/70.backend/backend/vhdl/vhdl_design_catalog.spl` :: `_sffi_dict_contains`
