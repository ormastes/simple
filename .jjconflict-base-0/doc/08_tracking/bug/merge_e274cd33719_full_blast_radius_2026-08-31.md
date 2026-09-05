# Full blast radius of merge e274cd33719 (share-history worktree merge clobber)

Date: 2026-08-31. Extends the boot-lane audit (record
`merge_e274cd33719_clobbered_x86_64_boot_lane_sources_2026-08-31.md`, which was
never landed on origin — it exists only in the authoring lane; method
reproduced independently here and cross-checked below).

## Scope correction

The briefed figure of "992 files" undercounts. The actual diff
`e274cd33719~1..e274cd33719` (single-parent snapshot commit, not a true merge;
parent `0fce018eda3`) touches **39,616 paths**: 29,389 M, 10,189 A, 34 D, 4 T.
Bulk is test/ (17,822) and doc/ (11,422); priority code area
(src/ + scripts/ + examples/09_embedded/simple_os/) has **5,583 modified files**.

## Method

Scripted (see `scratchpad/classify2.shs`, `verify_regressions.shs` in session
scratchpad): one-pass `git diff --raw/--numstat` joins, clobber candidate =
deletions >= 30 and > 3x additions; candidate's merge blob searched in the
parent-side history of the path (exact match = clean revert to an older
generation, no match = stale-forward snapshot); every candidate's origin status
computed after `git fetch` (`e274cd33719` IS an ancestor of origin/main, so the
column is valid). Both-directions rule satisfied mechanically for restores:
restore only where the merge blob is byte-identical to a historical ancestor
generation (parent is then a strict later generation) AND origin/main still
carries the merge blob (no landed fix is reverted).

## Classification counts (priority code areas)

- Clobber candidates (big-shrink M files): **864** of 5,583.
  - **627 ORIGIN_RESTORED_PARENT** — origin/main already carries the exact
    pre-merge blob. Damage repaired upstream; no action.
  - **74 ORIGIN_MOVED_PAST** — origin differs from both merge and parent.
    DO NOT restore (anti-revert protocol); listed below for review.
  - **163 live** (origin/main still == merge content):
    - **15 EXACT_OLD_GEN** — merge reverted to a byte-identical older blob
      (generations dated 2026-08-11 / 08-21 / 08-22). RESTORED in this change
      from `e274cd33719~1` (+1737/-126). List below.
    - **148 STALE_FORWARD** — merge content matches no ancestor blob (old base
      plus new edits, the classic stale-snapshot shape). FLAGGED for human
      review; cannot mechanically pick a side. List below.
- Deletions: 34 total; 7 restored on origin; **27 still deleted** — mostly
  build artifacts (bin/simple.exe, target_wt/, tauri gen/), but note
  `test/01_unit/lib/test_runner/zero_executed_abort_no_results_line_spec.spl`
  + its bug record and 3 `examples/11_advanced/game3d_*` mains — review.
- Unable to classify: candidates outside the big-shrink heuristic (small or
  balanced edits) were NOT deep-checked — 5,583-864 = 4,719 priority M files
  screened only by numstat; plus test/, doc/, tools/ etc. not deep-audited.

## Cross-check against the boot-lane audit

`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`
(-2665/+441) and `gui_entry_desktop.spl` (-393/+80) rank #1 and high on the
live candidate list — the confirmed-damaged files reproduce under this method.
They classify STALE_FORWARD/live here because the other lane's restorations
are NOT on origin/main yet; they are left to that lane (not re-restored here).

## Restored in this change (15 files, clean reverts, origin unmoved)

- `src/os/tools/simplebox/simplebox_fs_applets.spl` (-465/+18, merge content = from=7003f628bd8cba97720f454858ceb993eb7fdd31 2026-08-22)
- `src/os/kernel/net/thread_shim.spl` (-288/+15, merge content = from=ae55a7467197350bdf8b91c48444c167219ce8bb 2026-08-11)
- `src/os/kernel/arch/arm32/paging.spl` (-200/+0, merge content = from=ae55a7467197350bdf8b91c48444c167219ce8bb 2026-08-11)
- `src/os/port/simpleos_32bit_bootstrap_contract.spl` (-163/+11, merge content = from=4790b656ea5b18983b6aeda5299934333c539136 2026-08-22)
- `src/app/sj_daemon/forbidden.spl` (-116/+4, merge content = from=ae55a7467197350bdf8b91c48444c167219ce8bb 2026-08-11)
- `src/os/services/wm/wm_damage.spl` (-79/+2, merge content = from=4b88aebf00b750b5b328dfc70db416062ebb52a0 2026-08-21)
- `src/os/kernel/boot/mmio_hardware.spl` (-76/+19, merge content = from=ae55a7467197350bdf8b91c48444c167219ce8bb 2026-08-11)
- `src/os/drivers/pci/pci_provider.spl` (-55/+1, merge content = from=ae55a7467197350bdf8b91c48444c167219ce8bb 2026-08-11)
- `src/app/compiler_schema/extract.spl` (-55/+18, merge content = from=4b88aebf00b750b5b328dfc70db416062ebb52a0 2026-08-21)
- `src/os/installer/image_builder_payloads.spl` (-49/+6, merge content = from=4b88aebf00b750b5b328dfc70db416062ebb52a0 2026-08-21)
- `src/os/services/evidence/capability_ledger.spl` (-43/+8, merge content = from=4b88aebf00b750b5b328dfc70db416062ebb52a0 2026-08-21)
- `src/app/compiler_schema/main.spl` (-39/+1, merge content = from=4b88aebf00b750b5b328dfc70db416062ebb52a0 2026-08-21)
- `src/app/cli/query_helpers.spl` (-37/+11, merge content = from=ae55a7467197350bdf8b91c48444c167219ce8bb 2026-08-11)
- `src/os/services/netstack/_NetstackService/ipc_handlers.spl` (-36/+9, merge content = from=ae55a7467197350bdf8b91c48444c167219ce8bb 2026-08-11)
- `src/app/test/torch_cuda_optimizer_probe.spl` (-36/+3, merge content = from=ae55a7467197350bdf8b91c48444c167219ce8bb 2026-08-11)

## FLAGGED — live stale-forward clobber suspects (148, top 60 by lines lost)

Origin still carries the merge content; merge content is not any historical
generation. Each needs a both-directions diff by a human/owning lane.

- `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c` (-2665/+441)
- `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` (-1282/+235)
- `src/os/kernel/loader/executable_authority_registry.spl` (-1123/+148)
- `src/app/release/main.spl` (-810/+86)
- `src/os/services/tty_service.spl` (-692/+31)
- `src/os/kernel/ipc/capability.spl` (-485/+56)
- `src/verification/kernel_scheduler/KernelScheduler/Theorems.lean` (-478/+0)
- `src/app/compiler_schema/visitor_gen.spl` (-474/+40)
- `examples/09_embedded/simple_os/arch/x86_64/wm_entry.spl` (-460/+148)
- `src/os/crypto/ml_kem.spl` (-436/+19)
- `src/os/libc/simpleos_libc_ext.c` (-420/+16)
- `src/app/office/sheets/number_format.spl` (-397/+72)
- `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl` (-393/+80)
- `src/os/drivers/audio/hda_controller.spl` (-381/+22)
- `src/verification/actor_channel/ActorChannel/Theorems.lean` (-357/+6)
- `src/app/wm_compare/backend_measurement_report.spl` (-349/+66)
- `src/app/office/word/word_app.spl` (-349/+102)
- `src/app/office/sheets/data_ops.spl` (-347/+1)
- `src/os/libc/simpleos_socket.c` (-317/+18)
- `src/os/drivers/framebuffer/fb_driver.spl` (-293/+44)
- `src/os/compositor/cursor.spl` (-288/+0)
- `src/app/llm_dashboard/data/types.spl` (-283/+4)
- `src/app/ui.electron/bridge.js` (-275/+4)
- `src/os/apps/dbd/dbd_protocol.spl` (-265/+47)
- `src/os/kernel/arch/arm32/cosmos/cosmos_uart.c` (-258/+12)
- `src/os/kernel/memory/vmm_vma.spl` (-257/+68)
- `src/os/services/vfs/vfs.spl` (-251/+79)
- `src/os/kernel/arch/arm32/cosmos/cosmos_pcie.c` (-246/+44)
- `src/os/apps/sshd/ssh_channel.spl` (-246/+31)
- `src/verification/kernel_capabilities/KernelCapabilities/Theorems.lean` (-242/+19)
- `src/os/services/pm_service.spl` (-234/+52)
- `src/os/kernel/boot/dtb_parser.spl` (-233/+73)
- `src/os/compositor/engine2d_baremetal_core.spl` (-233/+10)
- `src/app/sspec_maintain/source_facts.spl` (-231/+13)
- `src/app/office/sheets/chart.spl` (-230/+0)
- `src/app/office/word/html_render.spl` (-220/+8)
- `src/app/llm_caret/claude_full/bridge/bridgeMain.spl` (-211/+9)
- `examples/09_embedded/simple_os/arch/riscv32/boot/baremetal_stubs.c` (-206/+7)
- `src/os/kernel/arch/arm32/cosmos/cosmos_start.S` (-191/+1)
- `src/os/crypto/ml_kem_ntt.spl` (-187/+0)
- `src/app/portal/public/css/app.css` (-182/+0)
- `examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl` (-180/+33)
- `src/app/spipe_docgen/spipe_docgen/parser.spl` (-172/+27)
- `src/app/model3d/main.spl` (-172/+31)
- `src/os/libc/simpleos_libc.c` (-155/+2)
- `examples/09_embedded/simple_os/arch/riscv64/boot/tls13_aes256_gcm_helper.c` (-151/+0)
- `src/os/crypto/sha256.spl` (-141/+9)
- `src/app/llm_caret/claude_full/services/api/withRetry.spl` (-141/+13)
- `src/os/kernel/arch/arm32/cosmos/cosmos_runtime.c` (-140/+14)
- `src/os/crypto/pem.spl` (-136/+31)
- `src/os/kernel/arch/arm32/cosmos/cosmos_smp_gic.c` (-134/+1)
- `src/app/ide/capabilities.spl` (-134/+3)
- `examples/09_embedded/simple_os/arch/riscv64/boot/tls13_sha256_helper.c` (-133/+0)
- `src/os/services/wm/wm_host_2d_simpleos.spl` (-125/+24)
- `src/os/kernel/arch/riscv64/trap_vector.spl` (-124/+6)
- `src/os/desktop/z_order_store.spl` (-122/+5)
- `src/os/services/sched_service.spl` (-120/+33)
- `src/os/tls13/handshake13_ext_builders.spl` (-118/+1)
- `src/os/kernel/boot/mmio.spl` (-116/+16)
- `src/os/kernel/socket_compat.spl` (-115/+23)

(Full 148-file list: session scratchpad `blast2/live_verified.txt`.)

## DO NOT RESTORE — origin moved past (74)

- `src/lib/gc_async_mut/gpu/browser_engine/webgpu_context.spl` (-1109/+56)
- `src/compiler/70.backend/backend/vulkan_backend.spl` (-990/+136)
- `src/compiler/70.backend/backend/cuda_backend.spl` (-850/+200)
- `scripts/bootstrap/bootstrap-strategy.sh` (-826/+214)
- `src/app/cli/dispatch/table.spl` (-733/+15)
- `src/compiler/70.backend/backend/vhdl/vhdl_call_lowering.spl` (-591/+4)
- `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl` (-511/+108)
- `src/app/mcp/dap_types.spl` (-449/+29)
- `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl` (-425/+137)
- `src/compiler/70.backend/backend/vhdl_validation.spl` (-403/+50)
- `scripts/check/lib/bootstrap-stage3/sanity.shs` (-391/+66)
- `src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl` (-388/+42)
- `src/lib/nogc_sync_mut/sffi/dynamic.spl` (-343/+49)
- `src/app/office/file_formats.spl` (-323/+47)
- `src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl` (-300/+68)
- `src/compiler/90.tools/lint/_LintMain/config_and_model.spl` (-294/+75)
- `src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl` (-290/+25)
- `src/compiler/80.driver/driver_aot_native_output.spl` (-264/+80)
- `src/lib/nogc_sync_mut/io_runtime.spl` (-261/+81)
- `src/lib/common/crypto/sha256.spl` (-256/+76)
- `src/lib/nogc_sync_mut/sffi/system.spl` (-256/+45)
- `src/app/mcp/main_lazy_query_tools.spl` (-242/+58)
- `src/compiler/10.frontend/core/_AstExpr/nodes.spl` (-240/+56)
- `scripts/check/check-guard-wiring.shs` (-234/+61)
- `scripts/check/check-push-must-pass.shs` (-223/+48)
- `scripts/check/check-no-direct-rt.shs` (-196/+55)
- `src/app/llm_caret/main.spl` (-190/+25)
- `src/app/llm_caret/config.spl` (-189/+7)
- `src/app/simple_lsp_mcp/main.spl` (-181/+40)
- `src/lib/common/json/parser.spl` (-168/+21)
- `src/app/office/slides/slide.spl` (-168/+14)
- `src/lib/nogc_sync_mut/sffi/io.spl` (-154/+33)
- `src/compiler/70.backend/backend/vhdl_entity_compile.spl` (-137/+38)
- `src/compiler/80.driver/driver_hir_pipeline_passes.spl` (-135/+44)
- `src/compiler/55.borrow/borrow_check/borrow_graph.spl` (-126/+23)
- `src/lib/nogc_sync_mut/web_framework/tracing.spl` (-124/+4)
- `src/compiler/20.hir/hir_lowering/module_surface_registry.spl` (-121/+10)
- `src/compiler/20.hir/hir_symbol_table_methods.spl` (-116/+1)
- `src/lib/nogc_sync_mut/test_runner/test_runner_types.spl` (-116/+13)
- `src/lib/nogc_sync_mut/spec.spl` (-106/+26)
- `src/compiler/60.mir_opt/optimizer_plugin.spl` (-104/+8)
- `scripts/audit/direct-env-runtime-guard.shs` (-102/+22)
- `src/lib/scv/merge.spl` (-95/+30)
- `src/os/_QemuRunner/scenario_catalog.spl` (-93/+23)
- `src/app/scv/main.spl` (-92/+15)
- `scripts/check/check-llm-tooling-public-absence-rendering.shs` (-91/+0)
- `src/os/apps/sshd/ssh_session_lifecycle.spl` (-85/+9)
- `src/compiler/10.frontend/core/interpreter/eval_access.spl` (-85/+25)
- `src/app/test_daemon/light_daemon.spl` (-85/+17)
- `src/app/llm_caret/json_helpers.spl` (-83/+9)
- `src/app/llm_caret/openai_compat.spl` (-83/+21)
- `src/compiler/70.backend/backend/vhdl/vhdl_abi.spl` (-77/+13)
- `src/lib/nogc_async_mut/sffi/llvm_target.spl` (-73/+11)
- `src/app/mcp/main_static_tools.spl` (-70/+13)
- `scripts/check/no_direct_rt_allowlist.txt` (-63/+15)
- `scripts/check/check-simpleos-mission-critical-release.shs` (-59/+3)
- `src/app/mcp/main_lazy_diag_tools.spl` (-58/+17)
- `src/compiler/10.frontend/core/interpreter/eval_builtins.spl` (-57/+1)
- `src/compiler/10.frontend/desugar/collection_desugar.spl` (-57/+12)
- `src/app/office/sheets/spreadsheet.spl` (-54/+6)
- `src/compiler/70.backend/backend/c_type_mapper.spl` (-53/+16)
- `scripts/check/check-ui-backend-isolation.shs` (-52/+5)
- `src/compiler/70.backend/linker/platform_defaults.spl` (-51/+9)
- `scripts/check/check_jit_interpreter_differential.spl` (-51/+3)
- `src/compiler/70.backend/backend/llvm_backend.spl` (-49/+15)
- `src/os/port/_SimpleosMultiplatformBuild/platform_target_catalog.spl` (-47/+4)
- `src/compiler/80.driver/driver_public_headers.spl` (-45/+11)
- `src/lib/common/engine/math3d.spl` (-36/+2)
- `src/compiler/20.hir/hir_lowering/_Items/module_callable_types.spl` (-35/+10)
- `src/lib/nogc_sync_mut/spec/engine_probe.spl` (-33/+10)
- `src/compiler/10.frontend/core/interpreter/__init__.spl` (-33/+10)
- `src/app/mcp/main_dispatch.spl` (-32/+2)
- `scripts/check/guard_wiring_unwired_baseline.txt` (-32/+0)
- `src/lib/common/js/engine/vm_object_store.spl` (-31/+4)

## Recommended actions

1. Land the 15 restorations (this change). Do not push without the standard guards.
2. Owning lanes triage the 148 flagged stale-forward files, boot lane first
   (baremetal_stubs.c, wm_entry.spl, gui_entry_desktop.spl,
   engine2d_baremetal_core.spl already in hand elsewhere — land them).
3. Review the 27 still-deleted paths; likely-real losses:
   zero_executed_abort spec + bug record, game3d examples.
4. Nothing in the ORIGIN_MOVED_PAST list may be restored from pre-merge.

## Appendix: full live stale-forward list (148)

- `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c` (-2665/+441)
- `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` (-1282/+235)
- `src/os/kernel/loader/executable_authority_registry.spl` (-1123/+148)
- `src/app/release/main.spl` (-810/+86)
- `src/os/services/tty_service.spl` (-692/+31)
- `src/os/kernel/ipc/capability.spl` (-485/+56)
- `src/verification/kernel_scheduler/KernelScheduler/Theorems.lean` (-478/+0)
- `src/app/compiler_schema/visitor_gen.spl` (-474/+40)
- `examples/09_embedded/simple_os/arch/x86_64/wm_entry.spl` (-460/+148)
- `src/os/crypto/ml_kem.spl` (-436/+19)
- `src/os/libc/simpleos_libc_ext.c` (-420/+16)
- `src/app/office/sheets/number_format.spl` (-397/+72)
- `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl` (-393/+80)
- `src/os/drivers/audio/hda_controller.spl` (-381/+22)
- `src/verification/actor_channel/ActorChannel/Theorems.lean` (-357/+6)
- `src/app/wm_compare/backend_measurement_report.spl` (-349/+66)
- `src/app/office/word/word_app.spl` (-349/+102)
- `src/app/office/sheets/data_ops.spl` (-347/+1)
- `src/os/libc/simpleos_socket.c` (-317/+18)
- `src/os/drivers/framebuffer/fb_driver.spl` (-293/+44)
- `src/os/compositor/cursor.spl` (-288/+0)
- `src/app/llm_dashboard/data/types.spl` (-283/+4)
- `src/app/ui.electron/bridge.js` (-275/+4)
- `src/os/apps/dbd/dbd_protocol.spl` (-265/+47)
- `src/os/kernel/arch/arm32/cosmos/cosmos_uart.c` (-258/+12)
- `src/os/kernel/memory/vmm_vma.spl` (-257/+68)
- `src/os/services/vfs/vfs.spl` (-251/+79)
- `src/os/kernel/arch/arm32/cosmos/cosmos_pcie.c` (-246/+44)
- `src/os/apps/sshd/ssh_channel.spl` (-246/+31)
- `src/verification/kernel_capabilities/KernelCapabilities/Theorems.lean` (-242/+19)
- `src/os/services/pm_service.spl` (-234/+52)
- `src/os/kernel/boot/dtb_parser.spl` (-233/+73)
- `src/os/compositor/engine2d_baremetal_core.spl` (-233/+10)
- `src/app/sspec_maintain/source_facts.spl` (-231/+13)
- `src/app/office/sheets/chart.spl` (-230/+0)
- `src/app/office/word/html_render.spl` (-220/+8)
- `src/app/llm_caret/claude_full/bridge/bridgeMain.spl` (-211/+9)
- `examples/09_embedded/simple_os/arch/riscv32/boot/baremetal_stubs.c` (-206/+7)
- `src/os/kernel/arch/arm32/cosmos/cosmos_start.S` (-191/+1)
- `src/os/crypto/ml_kem_ntt.spl` (-187/+0)
- `src/app/portal/public/css/app.css` (-182/+0)
- `examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl` (-180/+33)
- `src/app/model3d/main.spl` (-172/+31)
- `src/app/spipe_docgen/spipe_docgen/parser.spl` (-172/+27)
- `src/os/libc/simpleos_libc.c` (-155/+2)
- `examples/09_embedded/simple_os/arch/riscv64/boot/tls13_aes256_gcm_helper.c` (-151/+0)
- `src/os/crypto/sha256.spl` (-141/+9)
- `src/app/llm_caret/claude_full/services/api/withRetry.spl` (-141/+13)
- `src/os/kernel/arch/arm32/cosmos/cosmos_runtime.c` (-140/+14)
- `src/os/crypto/pem.spl` (-136/+31)
- `src/app/ide/capabilities.spl` (-134/+3)
- `src/os/kernel/arch/arm32/cosmos/cosmos_smp_gic.c` (-134/+1)
- `examples/09_embedded/simple_os/arch/riscv64/boot/tls13_sha256_helper.c` (-133/+0)
- `src/os/services/wm/wm_host_2d_simpleos.spl` (-125/+24)
- `src/os/kernel/arch/riscv64/trap_vector.spl` (-124/+6)
- `src/os/desktop/z_order_store.spl` (-122/+5)
- `src/os/services/sched_service.spl` (-120/+33)
- `src/os/tls13/handshake13_ext_builders.spl` (-118/+1)
- `src/os/kernel/boot/mmio.spl` (-116/+16)
- `src/os/kernel/socket_compat.spl` (-115/+23)
- `src/os/tls13/handshake13_hrr.spl` (-112/+12)
- `src/os/kernel/loader/elf_loader.spl` (-109/+3)
- `src/os/libc/simpleos_fork.c` (-107/+4)
- `src/os/kernel/arch/arm32/cosmos/cosmos_linker.ld` (-105/+13)
- `src/os/kernel/ipc/ipc.spl` (-103/+33)
- `src/os/tls13/_Tls13/context_io.spl` (-101/+22)
- `src/os/compositor/screenshot_compare.spl` (-99/+4)
- `src/os/kernel/ipc/cspace_spawn.spl` (-97/+1)
- `src/os/kernel/arch/riscv64/platform/boot_profile.spl` (-96/+2)
- `src/os/userlib/fs.spl` (-94/+6)
- `src/os/port/llvm/sysroot.shs` (-91/+15)
- `src/app/doc_coverage/analysis/sdoctest_coverage.spl` (-89/+2)
- `src/os/libc/simpleos_fs.c` (-87/+5)
- `src/app/ui.web/wm.js` (-85/+5)
- `src/os/compositor/hosted_backend_winit.spl` (-83/+19)
- `src/app/dashboard/main.spl` (-83/+10)
- `src/os/services/vfs/vfs_service.spl` (-82/+18)
- `src/os/tls13/handshake13.spl` (-80/+4)
- `src/app/editor/editor_controller.spl` (-79/+26)
- `src/os/tls13/server.spl` (-79/+13)
- `src/os/kernel/net/http_baremetal.spl` (-78/+8)
- `src/os/lib/gpu_bridge/host_gpu_ivshmem.spl` (-78/+18)
- `src/os/services/ds_service.spl` (-77/+24)
- `src/os/tls13/record13.spl` (-77/+20)
- `src/os/compositor/simple_gui_hosted_wm.spl` (-74/+14)
- `src/os/libc/simpleos_cxxabi.c` (-74/+0)
- `src/os/userlib/_Window/client_methods.spl` (-73/+17)
- `src/os/kernel/loader/app_registry.spl` (-70/+14)
- `src/os/compositor/shared_mdi_setup.spl` (-69/+7)
- `src/os/tls13/server_handshake.spl` (-69/+12)
- `src/os/kernel/loader/container_namespace.spl` (-68/+0)
- `src/os/kernel/memory/memory_swap_runtime.spl` (-67/+8)
- `src/os/kernel/ipc/message_buffer.spl` (-67/+0)
- `src/os/tools/simplebox/simplebox_dispatch.spl` (-66/+15)
- `src/app/llm_caret/claude_full/query.spl` (-66/+0)
- `src/app/editor/editor_ctrl_core.spl` (-62/+2)
- `examples/09_embedded/simple_os/arch/riscv64/boot/ghdl_boot_info_runtime.c` (-62/+20)
- `src/verification/db_storage/DbStorage/Theorems.lean` (-62/+0)
- `src/os/kernel/memory/memory_owned_pages.spl` (-61/+8)
- `src/os/crypto/aes128_gcm.spl` (-61/+19)
- `examples/09_embedded/simple_os/arch/x86_64/boot/primitives.c` (-61/+15)
- `examples/09_embedded/simple_os/arch/x86_32/initrd_fs_exec_probe_entry.spl` (-56/+0)
- `src/os/compositor/frame_pacer.spl` (-55/+8)
- `examples/09_embedded/simple_os/arch/x86_64/boot/crt0.s` (-54/+6)
- `src/app/desugar/context_params.spl` (-54/+17)
- `src/os/kernel/boot/tcp_baremetal_min.spl` (-53/+3)
- `src/app/ui.electron/bridge_envelopes.js` (-52/+1)
- `examples/09_embedded/simple_os/arch/riscv64/boot/full_networking_runtime.c` (-52/+1)
- `src/os/userlib/process.spl` (-52/+12)
- `src/os/port/llvm/build.shs` (-51/+9)
- `src/os/kernel/memory/vmm_copy.spl` (-50/+3)
- `src/os/kernel/memory/vmm_core.spl` (-48/+9)
- `src/app/debug/remote/protocol/gdb_mi_parser.spl` (-48/+9)
- `src/os/toolchain/llvm/simpleos_cross_toolchain.cmake` (-48/+3)
- `examples/09_embedded/simple_os/arch/x86_64/boot/tls13_aes256_gcm_helper.c` (-48/+2)
- `src/app/llm_runtime/serve_plan.spl` (-48/+11)
- `src/app/office/sheets/cond_format.spl` (-48/+10)
- `src/app/llm_dashboard/collectors/diagnostics_jsonl_collector.spl` (-47/+8)
- `src/os/kernel/ipc/host_gpu_ivshmem_map.spl` (-47/+2)
- `src/app/play/main.spl` (-46/+4)
- `src/os/libc/simpleos_process_wait.c` (-45/+0)
- `src/app/memstat/main.spl` (-44/+5)
- `src/os/hosted/hosted_browser_renderer_policy.spl` (-43/+11)
- `src/os/apps/dbd/dbd_launch.spl` (-42/+1)
- `src/app/office/sheets/sheets_app.spl` (-41/+2)
- `src/app/llm_runtime/manifest.spl` (-41/+1)
- `src/os/libc/include/sys/socket.h` (-40/+3)
- `src/app/office/slides/html_render.spl` (-39/+6)
- `src/os/kernel/loader/primary_linux_tool_catalog_bundle_v1.spl` (-39/+4)
- `src/os/drivers/virtio/virtio_net_async.spl` (-39/+12)
- `src/os/libc/include/wchar.h` (-38/+1)
- `src/os/services/devfs_service.spl` (-38/+12)
- `examples/09_embedded/simple_os/arch/riscv64/boot/ed25519_scalar_helper.c` (-36/+6)
- `src/app/llm_dashboard/main.spl` (-36/+11)
- `src/verification/riscv_product/src/RiscvProduct/Generated.lean` (-35/+4)
- `src/os/services/rs_service.spl` (-35/+10)
- `src/os/kernel/arch/arm64/ramfb.spl` (-35/+0)
- `src/os/services/pipefs_service.spl` (-34/+9)
- `src/app/ui.browser/event_bridge.spl` (-34/+9)
- `src/verification/kernel_capabilities/KernelCapabilities/Basic.lean` (-34/+0)
- `src/os/ml/gpu_tensor.spl` (-33/+5)
- `src/verification/kernel_scheduler/KernelScheduler/Basic.lean` (-33/+1)
- `src/app/portal/services/auth_service.spl` (-33/+0)
- `src/os/userlib/net.spl` (-32/+1)
- `src/os/libc/simpleos_math_ext.c` (-32/+0)
- `src/verification/riscv_product/src/RiscvProduct/Constraints.lean` (-31/+6)
- `examples/09_embedded/simple_os/arch/common/linker_riscv_common.ld` (-30/+5)
- `src/os/libc/simpleos_string_ext.c` (-30/+0)

## Landing caveats

- Staleness window: the ORIGIN_EQ_MERGE column was computed from one fetch
  during this session; parallel lanes push continuously. Before landing the 15
  restorations, re-fetch and re-verify `origin/main:<path>` still equals the
  merge blob for each — otherwise a concurrent fix gets clobbered.
- Coverage boundary: deep checks ran only on priority-area M files passing the
  big-shrink heuristic (864 of 5,583). Not deep-checked: 4,719 small/balanced
  priority M files, ~29k test/+doc/ paths, and the 10,189 A files (an added
  file can also resurrect stale content).
