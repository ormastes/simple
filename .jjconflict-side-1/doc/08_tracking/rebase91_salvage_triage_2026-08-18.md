# REBASE91 salvage triage — 108 uncherry-pickable commits (2026-08-18)

Base: origin/main d425c97ee7f. Fork merge-base: 488f622ae12. Lane tip: 92f7850dd64.

## Buckets
| bucket | count | disposition |
|---|---|---|
| ADAPTABLE (replayed as-is, `cherry-pick -x`) | 33 | landed |
| ADAPTABLE (path-level salvage, origin never touched path) | 168 paths | landed |
| ADAPTABLE (clean 3-way merge, origin's side preserved) | 35 paths (23 effective) | landed |
| SUPERSEDED | 333 paths | abandoned — origin already byte-identical to lane tip |
| DIVERGENT | 115 paths | abandoned — both sides changed the same logic, authoring lane must choose |
| POISON | 49 paths (commit 94afb1dd7d6) | abandoned — aliased `use std.io_runtime.{x as y}` does not survive co-compilation |
| TIP-DELETED | 2 paths | abandoned — lane deleted a file origin still carries |

## Abandoned: DIVERGENT paths
- doc/08_tracking/bug/array_guarded_method_names_no_mir_dispatch_2026-08-17.md
- doc/08_tracking/bug/codegen_lane_still_slow_base64url_utf8_time_utils_2026-08-18.md
- doc/08_tracking/bug/const_generic_argument_rejected_in_constructor_call_2026-08-17.md
- doc/08_tracking/bug/fstring_nested_quoted_literal_in_interpolation_misparsed_2026-08-17.md
- doc/08_tracking/bug/guard_silent_nonzero_exit_no_verdict_line_2026-08-17.md
- doc/08_tracking/bug/i8_array_literal_reads_back_wrong_value_2026-08-17.md
- doc/08_tracking/bug/interp_array_param_indexing_2026-07-03.md
- doc/08_tracking/bug/native_build_source_closure_zero_sources_2026-08-17.md
- doc/08_tracking/bug/native_build_worker_timeout_blocks_all_pushes_2026-08-17.md
- doc/08_tracking/bug/office_render_adapter_unknown_name_and_naming_drift_2026-07-20.md
- doc/08_tracking/bug/parser_bracket_index_after_less_than_still_misread_as_generics_2026-08-17.md
- doc/08_tracking/bug/rt_dir_list_platform_header_collides_with_extern_2026-08-10.md
- doc/08_tracking/bug/stage4_bootstrap_rust_inputs_changed_2026-08-15.md
- doc/08_tracking/c_migration/c_migration_inventory.sdn
- doc/08_tracking/c_migration/c_replaceable_bug_list.md
- scripts/bootstrap/resume-stage3-from-admitted.sh
- scripts/check/check-binary-sspec-evidence.shs
- scripts/check/check-bootstrap-planner-admission-producer.shs
- scripts/check/check-build-outcome-reason-attribution.shs
- scripts/check/check-no-direct-rt.shs
- scripts/check/lib/bootstrap-planner-admission-bound.shs
- scripts/check/no_direct_rt_allowlist.txt
- scripts/spipe/rt_migration_cycle.shs
- .spipe/unstable_test_mode/state.md
- src/app/check/main.spl
- src/app/check/wm_lane_boundary_check.spl
- src/app/cli/check_tier.spl
- src/app/cli/native_build_main.spl
- src/app/cli/query_check.spl
- src/app/cli/query_commands.spl
- src/app/compile/llvm_direct.spl
- src/app/compile/lua_shared_lib.spl
- src/app/compile/native.spl
- src/app/container_packaging/build.spl
- src/app/dap/simple_dap_main.spl
- src/app/dashboard/framework_policy.spl
- src/app/deps/scanner.spl
- src/app/doc/public_check/docstring_checker.spl
- src/app/doc/public_check/export_parser.spl
- src/app/editor/editor_attachment_template.spl
- src/app/editor/mcp_tools_helpers.spl
- src/app/game/new.spl
- src/app/game/run.spl
- src/app/grammar_doc/mod.spl
- src/app/gui_perf/smf_dynlib_probe_core.spl
- src/app/io/_CliCommands/handler_commands.spl
- src/app/io/_CliCommands/run_commands.spl
- src/app/io/cli_ops.spl
- src/app/js/main.spl
- src/app/llm_caret/tools.spl
- src/app/llm_dashboard/collectors/remote_collector.spl
- src/app/llm_dashboard/collectors/schedule_collector.spl
- src/app/llm_dashboard/main.spl
- src/app/llm_dashboard/scheduler/scheduler.spl
- src/app/llm_process_gen/main.spl
- src/app/play/orchestrator.spl
- src/app/play/session_store.spl
- src/app/repl/main.spl
- src/app/simpleos_tool/focused_pipeline.spl
- src/app/simple_portal/server.spl
- src/app/snpm/installer.spl
- src/app/snpm/lockfile.spl
- src/app/snpm/manifest.spl
- src/app/spipe_process_harness/main.spl
- src/app/task_daemon/main.spl
- src/app/test/bench/bench_baseline_driver.spl
- src/app/test/bench/bench_report.spl
- src/app/test_daemon/adapters/container_adapter.spl
- src/app/test_daemon/adapters/gui_adapter.spl
- src/app/test_daemon/adapters/hardware_adapter.spl
- src/app/test_daemon/adapters/qemu_adapter.spl
- src/app/test_daemon/adapters/service_adapter.spl
- src/app/test_daemon/agent_client.spl
- src/app/test_daemon/daemon.spl
- src/app/test_daemon/light_daemon.spl
- src/app/test_daemon/main.spl
- src/app/test_daemon/manifest_daemon.spl
- src/app/test_daemon/qemu_broker.spl
- src/app/test_daemon/session_types.spl
- src/app/test_dep_graph_shared.spl
- src/app/test_runner_new/test_runner_client.spl
- src/app/test_runner_new/test_runner_single.spl
- src/app/ui.cli/socket_server.spl
- src/app/ui.electron/async_app.spl
- src/app/ui.tui/app.spl
- src/app/ui.tui/async_app.spl
- src/app/watch/deps.spl
- src/compiler/80.driver/driver_build/build_outcome.spl
- src/compiler/95.interp/mir_interpreter.spl
- src/compiler_rust/compiler/src/mem_trace.rs
- src/lib/nogc_async_mut/async/runtime.spl
- src/lib/nogc_async_mut/async/sleep.spl
- src/lib/nogc_async_mut/io/udp_server.spl
- src/lib/nogc_sync_mut/daemon_sdk/client.spl
- src/lib/nogc_sync_mut/daemon_sdk/daemon.spl
- src/lib/nogc_sync_mut/daemon_sdk/lock.spl
- src/lib/nogc_sync_mut/daemon_sdk/protocol.spl
- src/lib/nogc_sync_mut/database/atomic.spl
- src/lib/nogc_sync_mut/database/nosql_offload.spl
- src/lib/nogc_sync_mut/db/dbfs_engine/meta_store.spl
- src/lib/nogc_sync_mut/desktop/lifecycle.spl
- src/lib/nogc_sync_mut/io/telnet_serial_bridge.spl
- src/lib/nogc_sync_mut/js/node/fs_module.spl
- src/lib/nogc_sync_mut/notebook/gpu_config.spl
- src/lib/nogc_sync_mut/notebook/local_exec.spl
- src/lib/nogc_sync_mut/notebook/lsp_bridge.spl
- src/lib/nogc_sync_mut/play/trace.spl
- src/lib/nogc_sync_mut/service/audit_log.spl
- src/lib/nogc_sync_mut/service/lifecycle.spl
- src/lib/nogc_sync_mut/spec/evidence/counterpart/artifact_store.spl
- src/lib/nogc_sync_mut/test_runner/test_manifest.spl
- src/lib/nogc_sync_mut/test_runner/test_runner_single.spl
- test/01_unit/compiler/driver/stage3_hir_lowerer_reuse_contract_spec.spl
- test/01_unit/lib/common/time_utils_crosslang_spec.spl
- test/01_unit/lib/nogc_sync_mut/hash_text_crosslang_spec.spl

## Abandoned: POISON paths (94afb1dd7d6, rt_ extern -> std.io_runtime wrapper migration)

Underlying compiler defect: an aliased import (`use std.io_runtime.{io_process_is_running as ...}`)
is not resolved under co-compilation — `Undefined: io_process_is_running`. This broke the Rust seed
and blocked every push. Any future re-land of this migration must use the direct extern, not an alias.
- scripts/check/no_direct_rt_baseline.txt
- src/app/io/file_shell.spl
- src/app/io/process_governor.spl
- src/app/io/vhdl_ffi.spl
- src/app/io/vhdl_sffi.spl
- src/app/release/install.spl
- src/app/test/ssh_live_boot_only.spl
- src/app/ui.cli/__init__.spl
- src/lib/nogc_sync_mut/database/sql/health.spl
- src/lib/nogc_sync_mut/database/sql/interceptor.spl
- src/lib/nogc_sync_mut/database/sql/retry.spl
- src/lib/nogc_sync_mut/debug/remote/test/qemu_runner.spl
- src/lib/nogc_sync_mut/fs.spl
- src/lib/nogc_sync_mut/gpu_profile/mem_profile.spl
- src/lib/nogc_sync_mut/i18n/bundle.spl
- src/lib/nogc_sync_mut/io/debug_stubs.spl
- src/lib/nogc_sync_mut/io/dir_ops.spl
- src/lib/nogc_sync_mut/io/env_ops.spl
- src/lib/nogc_sync_mut/io/file_ops.spl
- src/lib/nogc_sync_mut/io/file_shell.spl
- src/lib/nogc_sync_mut/io/process_governor.spl
- src/lib/nogc_sync_mut/io/ssh_serial.spl
- src/lib/nogc_sync_mut/io/thread.spl
- src/lib/nogc_sync_mut/io/time_ops.spl
- src/lib/nogc_sync_mut/io/vhdl_sffi.spl
- src/lib/nogc_sync_mut/js/node/child_process_module.spl
- src/lib/nogc_sync_mut/lsp/handlers/diagnostics.spl
- src/lib/nogc_sync_mut/lsp/lsp_handlers.spl
- src/lib/nogc_sync_mut/lsp/main.spl
- src/lib/nogc_sync_mut/mcp_sdk/core/shell.spl
- src/lib/nogc_sync_mut/package/dist.spl
- src/lib/nogc_sync_mut/platform/__init__.spl
- src/lib/nogc_sync_mut/platform/linker.spl
- src/lib/nogc_sync_mut/platform.spl
- src/lib/nogc_sync_mut/play/launcher.spl
- src/lib/nogc_sync_mut/play/sdl2_backend.spl
- src/lib/nogc_sync_mut/play/xvfb.spl
- src/lib/nogc_sync_mut/qemu/qmp_client.spl
- src/lib/nogc_sync_mut/shell/dir.spl
- src/lib/nogc_sync_mut/shell/env.spl
- src/lib/nogc_sync_mut/shell/file.spl
- src/lib/nogc_sync_mut/spec/env_detect.spl
- src/lib/nogc_sync_mut/spec/evidence/counterpart/worker_provider.spl
- src/lib/nogc_sync_mut/spec/skip_governance.spl
- src/lib/nogc_sync_mut/spec.spl
- src/lib/nogc_sync_mut/test_runner/resource_governor.spl
- src/lib/nogc_sync_mut/test_runner/system_monitor.spl
- src/lib/nogc_sync_mut/test_runner/test_runner_async.spl
- src/lib/nogc_sync_mut/ui_test/client.spl

## Replay outcome per commit
| sha | outcome |
|---|---|
| 47620eaee9e1 | CONFLICT |
| 78c342254b41 | CONFLICT |
| b8e0bdee12f6 | OK |
| d03b800c7d68 | CONFLICT |
| cf71cff7a486 | CONFLICT |
| bdeaf7262324 | FAILCONT |
| ed8c7325865d | CONFLICT |
| 34d24d20e7cd | CONFLICT |
| cafcc59ccefd | CONFLICT |
| f2326caec420 | CONFLICT |
| 136124ab07a8 | OK |
| f08f9547dc95 | CONFLICT |
| df0b2ca87471 | CONFLICT |
| c7584b189f11 | OK |
| acff67f28115 | CONFLICT |
| 999a794329e2 | CONFLICT |
| 3bb091c39a55 | CONFLICT |
| ca28abf10214 | OK |
| 731425ee3844 | OK |
| 545d6cad8f91 | CONFLICT |
| 7930368e8bea | OK |
| d81e0e98d975 | CONFLICT |
| c9aebe07ac15 | OK_RESOLVED_ADD |
| 0dcebb8ae3fd | OK |
| ce4deefb98cf | CONFLICT |
| aa76ff6133df | CONFLICT |
| fbd4ceeeb69d | OK |
| ab060d8ebe3f | OK |
| 047256836733 | OK |
| 91f2002ec5ad | OK |
| 813707363b40 | CONFLICT |
| 641d6f19d09d | CONFLICT |
| 17d3496f3f30 | CONFLICT |
| 0725be794d85 | CONFLICT |
| 91fa3cce4d4a | CONFLICT |
| 5c4d3eadea9a | OK |
| 9f608f1b32c4 | OK |
| 08c40c110f7d | OK |
| 5da202406dd2 | OK |
| beb8857a86fe | OK |
| dad95e5bfb58 | CONFLICT |
| e8816944d586 | CONFLICT |
| 6f40cbf14391 | OK |
| bcebe89b8312 | OK |
| 535f1e07e263 | OK |
| c89ca8acfc6e | OK_RESOLVED_ADD |
| a6e93f90707c | OK |
| 136360275826 | CONFLICT |
| 4e42ce0d32dc | CONFLICT |
| 9f5514d0bb23 | FAILCONT |
| c9c31af3d5ed | CONFLICT |
| d58c969c827a | CONFLICT |
| 29920b76f095 | CONFLICT |
| 50faff7aef90 | OK_RESOLVED_ADD |
| a663c1145b14 | OK |
| e5b58f7efc39 | OK |
| 172fc9f86a47 | OK |
| d0dbcccb1167 | CONFLICT |
| 9933fdac0a69 | CONFLICT |
| eb07a666256d | OK |
| 82cda476b6e2 | CONFLICT |
| 964af4ab0431 | CONFLICT |
| 9499e4c1f3d0 | OK |
| de5f922ae713 | CONFLICT |
| 0fa9744d4f48 | CONFLICT |
| a120359d8a50 | CONFLICT |
| 5f37845f640c | CONFLICT |
| 7604611185b6 | CONFLICT |
| 1a68c2b7bb14 | CONFLICT |
| 94afb1dd7d6c | POISON_SKIP |
| e357ef4835a9 | CONFLICT |
| be925afc17a1 | CONFLICT |
| 6dab6d90c5d4 | CONFLICT |
| 7ec2f750619d | CONFLICT |
| b5ebeb68499e | CONFLICT |
| 830c151272de | CONFLICT |
| eba632ef09ff | CONFLICT |
| dea1e957aa68 | CONFLICT |
| 492837f080c7 | CONFLICT |
| a850184c5d40 | CONFLICT |
| 3503f5ad6556 | CONFLICT |
| a0a62a3526f7 | CONFLICT |
| 6791d1b32503 | CONFLICT |
| ed00ad140671 | CONFLICT |
| 89d492cfa695 | CONFLICT |
| c61dbfd88fa9 | CONFLICT |
| 7ac413cb1142 | CONFLICT |
| cfdf5a0e2b15 | CONFLICT |
| 7754add5be3c | CONFLICT |
| caa4d7b8dff2 | OK |
| cb383eeb1af0 | CONFLICT |
| 248acbe57edf | CONFLICT |
| 553dec11a226 | OK |
| 6d46ef212f15 | OK_RESOLVED_ADD |
| 91efd6ef0975 | CONFLICT |
| 576144213a76 | CONFLICT |
| 48500ace49d1 | CONFLICT |
| 31e0eaa099cc | CONFLICT |
| 8db9943ef0ab | CONFLICT |
| 81dbfd5beaaa | CONFLICT |
| b3234f7b6872 | CONFLICT |
| f77fa2c4d192 | CONFLICT |
| bd0ea52b37cf | CONFLICT |
| 8961cb0b638e | CONFLICT |
| 55bada8b52f7 | OK |
| a7a7656b6f53 | CONFLICT |
| 67b4e089e4da | OK |
| 1ee17ab8147a | CONFLICT |
