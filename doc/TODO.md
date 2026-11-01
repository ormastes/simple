# TODO List

**Generated:** 2026-11-01
**Total:** 408 items | **Open:** 184 | **Blocked:** 58 | **Stale:** 0
**Database:** `doc/08_tracking/todo/todo_db.sdn`

## Statistics

### By Area

| Area | Count | P0 | P1 | P2 | P3 | Blocked |
|------|-------|----|----|----|----|---------|
| devhub | 1 | 0 | 1 | 0 | 0 | 1 |
| test_runner | 5 | 0 | 1 | 4 | 0 | 2 |
| general | 238 | 0 | 0 | 1 | 237 | 5 |
| gpu | 61 | 0 | 5 | 56 | 0 | 1 |
| compiler-resolver | 5 | 0 | 5 | 0 | 0 | 1 |
| llm-caret-server | 1 | 0 | 0 | 1 | 0 | 0 |
| llm-caret | 3 | 0 | 1 | 2 | 0 | 3 |
| debug | 2 | 0 | 0 | 2 | 0 | 0 |
| driver | 2 | 0 | 2 | 0 | 0 | 0 |
| sspec-live-capture | 1 | 0 | 0 | 1 | 0 | 1 |
| sspec-verification | 1 | 0 | 1 | 0 | 0 | 1 |
| llm-caret-messaging | 1 | 0 | 1 | 0 | 0 | 1 |
| sspec | 1 | 0 | 0 | 1 | 0 | 0 |
| infra | 1 | 0 | 0 | 0 | 1 | 0 |
| spipe_docgen | 1 | 0 | 0 | 1 | 0 | 0 |
| test | 2 | 0 | 1 | 1 | 0 | 0 |
| uno_q | 1 | 0 | 0 | 1 | 0 | 0 |
| cosmos | 1 | 1 | 0 | 0 | 0 | 0 |
| rendering | 1 | 1 | 0 | 0 | 0 | 0 |
| bootstrap | 3 | 0 | 2 | 1 | 0 | 1 |
| compiler | 10 | 1 | 7 | 2 | 0 | 5 |
| ui_slim | 7 | 0 | 2 | 2 | 3 | 6 |
| runtime | 11 | 0 | 2 | 9 | 0 | 3 |
| compositor | 1 | 0 | 0 | 1 | 0 | 0 |
| interpreter | 4 | 0 | 1 | 3 | 0 | 0 |
| freebsd | 3 | 0 | 2 | 1 | 0 | 3 |
| other-platform | 3 | 0 | 0 | 1 | 2 | 2 |
| simpleos | 5 | 0 | 1 | 1 | 3 | 4 |
| windows | 3 | 0 | 1 | 1 | 1 | 3 |
| type_system | 1 | 0 | 1 | 0 | 0 | 0 |
| interp | 1 | 0 | 0 | 1 | 0 | 0 |
| linux | 1 | 0 | 0 | 1 | 0 | 1 |
| build | 12 | 0 | 11 | 1 | 0 | 10 |
| container | 3 | 0 | 3 | 0 | 0 | 3 |
| lint | 5 | 0 | 0 | 5 | 0 | 0 |
| cache | 2 | 0 | 0 | 2 | 0 | 1 |
| hal | 1 | 0 | 0 | 1 | 0 | 0 |
| hash | 1 | 0 | 1 | 0 | 0 | 0 |
| 2D | 2 | 0 | 0 | 0 | 1 | 0 |

### By Priority

| Priority | Count | Open | Blocked | Stale |
|----------|-------|------|---------|-------|
| P0 (critical) | 3 | 3 | 1 | 0 |
| P1 (high) | 52 | 19 | 30 | 0 |
| P2 (medium) | 104 | 55 | 17 | 0 |
| P3 (low) | 248 | 106 | 10 | 0 |

## P0 - Critical

- **TODO** POSTPONED until identified Cosmos+ hardware and lab fixtures are available: execute and retain BT-001 through BT-006. The 2026-07-29 host audit found a Xilinx ML Carrier FT4232H (`XFL1OSWWFM2B`), a Lauterbach PODBUS controller, and three Samsung NVMe devices, but no Cosmos+/OpenSSD PCIe device. The repo-managed TRACE32 server reached TCP 20000, while read-only CPU, system, and `STATE.RUN()` queries all failed with exit 8128 because no target was configured. - `doc/08_tracking/todo/cosmos_nvme_firmware_remaining_2026-07-28.md:17`
- **TODO** BLOCKED: run the four-lane QEMU/container Vulkan mission showcase with an admitted self-hosted CLI, producer receipts, and an allocation-cap receipt; see TODO DB row 277 and this plan's resume command. - `doc/03_plan/sys_test/render_lane_mission_showcase.md:53`
- **TODO** Qualify macOS jobs=8 below 1000000000 bytes: SCV scratch/cold-batch fixes reduced the focused compile to 421707776 bytes, but Phase2 MIR errors blocked runtime correctness and canonical Stage3 verification after three cycles - `doc/08_tracking/bug/macos_scv_inventory_scratch_retention_2026-09-21.md:1` [blocked by: phase2-mir-local-index-reset-and-leaf-closure-pending-native-qualification]

## P1 - High Priority

- **TODO** Complete secured Messenger DB key-session open then secure SQLite snapshot and efficient bounded paging qualification - `doc/08_tracking/bug/devhub_secured_db_key_session_open_failure_2026_10_27.md:1` (#devhub_secured_db_key_session_open_failure_2026_10_27)
- **TODO** Verify macOS default and explicit max-procs policy plus safe-mode no-limits with source-matched Phase 2 full CLI and test runner - `doc/08_tracking/bug/test_runner_ulimit_caps_unusable_on_macos_2026-09-05.md:1`
- **TODO** `probe` is not a probe. It queries no device: it is a RESOLVED 2026-09-16: source no longer names this a probe — GraphicsCapabilities.from_policy documents 'does not inspect or confirm a live device'; db row was stale - `src/lib/gc_async_mut/gpu/session/graphics_capabilities.spl:30`
- **TODO** NO Metal device evidence exists on this machine, so no 2026-09-16 note: 2026-09-16: macOS-only evidence; cannot progress from a Windows host — Metal probe reports unavailable by construction here 2026-09-17 note: 2026-09-17: exercised on the Apple M4 host — still no Metal device evidence through the seed (metal_available() false; probe_error='metal runtime not available on this host'); Vulkan on the same host reports device_name=Apple M4, so the GPU is present and probeable; seed-side stub root cause recorded in doc/08_tracking/todo/gpu_metal_provider_probe_never_exercised_2026-09-06.md - `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl:75`
- **TODO** Remove this rename workaround once the seed resolves bare names by import scope instead of a global registry: a function's own parameter must win over a same-named imported module (doc/08_tracking/bug/module_name_shadows_function_parameter_2026-09-06.md) - `src/lib/nogc_sync_mut/http_server/server.spl:219`
- **TODO** SffiHttpMethod/SffiHttpResponse/SffiHttpStatus are named apart from http_server's HttpMethod/HttpResponse/HttpStatus only because the seed resolves type and enum-variant names globally by bare name; restore the plain names once resolution is import-scoped (doc/08_tracking/bug/enum_variant_resolved_globally_by_bare_name_httpmethod_collision_2026-09-06.md) - `src/lib/nogc_sync_mut/io/http_sffi.spl:122`
- **TODO** Reports every live agent as exited on the shipped binary: the seed's rt_process_is_running returns false for any pid it did not spawn and a tmux pane is tmux's child; fixed in source, needs the deploy (doc/08_tracking/bug/interpreter_process_is_running_false_for_unspawned_pid_2026-09-06.md) - `src/app/llm_caret/cs_dashboard.spl:497`
- **TODO** Verify Stage 3 self-hosting: the bootstrap has only ever reached 'Stage 2 admitted', and Stage 3 -- stage2 recompiling THIS file -- has never been attempted, so the byte-identical stage2 == stage3 fixpoint that the bootstrap claim rests on is unproven; see doc/08_tracking/bug/bootstrap_stage2_admission_refused_by_concurrent_source_edits_2026-09-05.md - `src/app/cli/bootstrap_main.spl:4`
- **TODO** T1 gate open: all Modern SSpec evidence verified on the Rust bootstrap seed. When a self-hosted binary is deployed, re-run the evidence specs + docgen gate on it - `test/03_system/tools/spipe/examples/live_capture_blocker_sentinels_spec.spl:48`
- **TODO** Run the Phase 4 full-CLI and Caret carrier verification with the exact source-matched candidate after Stage 4 admission; retain binary SHA-256, command outputs, and carrier provenance - `test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl:113`
- **TODO** Re-run every GPU scheduler spec on a redeployed full-CLI pure-Simple binary - `doc/08_tracking/todo/gpu_scheduler_specs_need_selfhosted_rerun_2026-09-06.md:1`
- **TODO** Restore canonical HTTP server parameter names after import-scoped resolution - `src/lib/nogc_sync_mut/http_server/server.spl:219` (#cc5894fce63)
- **TODO** Restore canonical HttpMethod/HttpStatus/HttpResponse names after import-scoped enum resolution - `src/lib/nogc_sync_mut/io/http_sffi.spl:122` (#4bb40d13b72)
- **TODO** Reconcile ten historical Stage-2 resolver symbols; nine are fixed or absent and virtual_source_store now reaches downstream projection - `src/compiler_rust/compiler/src/codegen/llvm/functions.rs:1` (#row-split-2026-09-14)
- **TODO** The 15 rt_gpu_session_metal_* / rt_cuda_* / rt_vk_* / rt_webgpu_* - `src/lib/gc_async_mut/gpu/session/backend_runtime_ops.spl:3`
- **TODO** Resolved: policy-derived graphics capabilities are named `from_policy`; unknown backends grant no capabilities and the API explicitly makes no device-probe claim - `src/lib/gc_async_mut/gpu/session/graphics_capabilities.spl:30` (#d3cd3a02824)
- **TODO** BLOCKED (bootstrap forbidden 2026-09-06): certified H0/T0/T1 startup on a deployed pure-Simple ui binary; seed numbers are diagnostic only - `doc/08_tracking/todo/ui_slim_kernel_plugin_wave3_blocked_2026-09-06.md:9`
- **TODO** BLOCKED: certified G0/G1 window timing on the deployed binary; launcher exit-141 and stale winit marker gate first - `doc/08_tracking/todo/ui_slim_kernel_plugin_wave3_blocked_2026-09-06.md:10`
- **TODO** Verify virtual_source_store through a minimal native Stage-2 link oracle; current focused integration reaches downstream summary projection rather than reproducing unresolved method dispatch - `src/compiler/00.common/cache_contract/virtual_source_registration_v1.spl:43`
- **TODO** Verify Stage 3 self-hosting: the bootstrap has only ever reached 'Stage 2 admitted', and Stage 3 -- stage2 recompiling THIS file -- has never been attempted, so the byte-identical stage2 == stage3 fixpoint that the bootstrap claim rests on is unproven; see doc/08_tracking/bug/bootstrap_stage2_admission_refused_by_concurrent_source_edits_2026-09-05.md - `src/app/cli/bootstrap_main.spl:6`
- **TODO** NO Metal device evidence exists on this machine, so no - `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl:75`
- **TODO** After Linux bootstrap succeeds, run canonical FreeBSD QEMU --full and verify the admitted Phase-2 compiler, interpreter, and loader binaries with command/status/time/max-RSS/log receipts using no more than 12 jobs - `doc/08_tracking/todo/freebsd_full_qemu_phase2_verification_2026-09-23.md:1`
- **TODO** Qualify optional-stdbuf and two-shell TMPDIR quoting with macos_process_live_spec.spl and Phase2 native fixture; verify cleanup with unusual paths; Phase2 has no test command and native compilation awaits cold SCV memory repair - `doc/08_tracking/todo/macos_bootstrap_process_live_qualification_2026-09-21.md:3`
- **TODO** Staged migration: reject Option patterns on non-Option scrutinees (measure, ratchet new code, convert sites in batches, hard error) - `doc/08_tracking/todo/option_pattern_non_option_scrutinee_migration_2026-09-27.md:1` (#option_pattern_non_option_scrutinee_migration_2026-09-27)
- **TODO** Finish item 7 typed planning, P6 metrics, generic coverage, guarded explain output, and admitted pure-Simple acceptance evidence - `doc/08_tracking/todo/profile_switchable_container_platform_qualification_2026-09-28.md:1`
- **TODO** Reduce source snapshot admission and materialization cost while preserving dependency invalidation and immutable source identity - `doc/08_tracking/todo/windows_source_snapshot_performance_2026-10-05.md:6`
- **TODO** Qualify the local fixed Docker attach fixture with exact bytes and destroy evidence - `doc/08_tracking/todo/dist_build_local_container_fixture_2026-09-26.md:1` (#dist_build_local_container_fixture_2026-09-26)
- **TODO** Provision two Linux workers and prove delegated cgroup V4 plus staged distributed execution - `doc/08_tracking/todo/dist_build_linux_two_node_qualification_2026-09-26.md:1` (#dist_build_linux_two_node_qualification_2026-09-26)
- **TODO** Build and qualify raw-sample N2 hook pre-push and warm-preflight benchmarks - `doc/08_tracking/todo/dist_build_n2_benchmark_2026-09-26.md:1` (#dist_build_n2_benchmark_2026-09-26)
- **TODO** Integrate signed local build evidence into reporting GitHub job with remote fallback - `doc/08_tracking/todo/dist_build_signed_ci_integration_2026-09-26.md:1` (#dist_build_signed_ci_integration_2026-09-26)
- **TODO** Implement and qualify native macOS Simple Container using shared SimpleOS lifecycle contracts - `doc/08_tracking/todo/native_macos_simple_container_2026-09-27.md:1` (#native_macos_simple_container_2026-09-27)
- **TODO** Diagnose macOS test runner monitor rt_process_spawn_async SIGSEGV in native memmove - `doc/08_tracking/bug/macos_test_runner_monitor_spawn_crash_2026-09-26.md:1` (#macos_test_runner_monitor_spawn_crash_2026-09-26)
- **TODO** Continue distributed-build host qualification from a clean Linux checkout with two scoped workers - `doc/08_tracking/todo/dist_build_other_host_qualification_2026-09-26.md:1` (#dist_build_other_host_qualification_2026-09-26)
- **TODO** Qualify shared Simple Container providers on Windows Server Linux FreeBSD and macOS with SDN receipts - `doc/08_tracking/todo/simple_container_cross_host_qualification_2026-09-26.md:1` (#simple_container_cross_host_qualification_2026-09-26)
- **TODO** Integrate and qualify parallel graph wave dispatch on two Linux workers - `doc/08_tracking/todo/dist_build_linux_parallel_wave_qualification_2026-09-27.md:1` (#dist_build_linux_parallel_wave_qualification_2026-09-27)
- **TODO** Bind signed fast-push receipts to immutable executed inputs - `doc/08_tracking/bug/dist_fast_push_receipt_input_race_2026-09-26.md:1` (#dist_fast_push_receipt_input_race_2026-09-26)
- **TODO** Qualify Linux rootless Simple Container lifecycle with non-root Podman and real exit/destroy evidence - `doc/08_tracking/todo/simple_container_linux_rootless_qualification_2026-09-27.md:1` (#simple_container_linux_rootless_qualification_2026-09-27)
- **TODO** Qualify handoff-bounded child result download and exact accepted bytes - `doc/08_tracking/bug/parallel_transport_child_download_budget_gap_2026-09-27.md:1` (#parallel_transport_child_download_budget_gap_2026-09-27)
- **TODO** Qualify streamed prepared upload and peak memory under parallel admission - `doc/08_tracking/bug/dist_build_prepared_upload_whole_file_memory_2026-09-27.md:1` (#dist_build_prepared_upload_whole_file_memory_2026-09-27)
- **TODO** Preserve process observation V4 lease or native cleanup proof after post-launch start decode failure - `doc/08_tracking/bug/process_observation_v4_unowned_start_decode_2026-09-27.md:1` (#process_observation_v4_unowned_start_decode_2026-09-27)
- **TODO** Publish isolated distributed-build draft PR after GitHub access is restored - `doc/08_tracking/todo/dist_build_pr_publication_2026-09-27.md:1` (#dist_build_pr_publication_2026-09-27)
- **TODO** Implement and qualify Windows Server HCS Simple Container lifecycle with selected client authority and real exit/destroy evidence - `doc/08_tracking/todo/simple_container_windows_server_qualification_2026-09-27.md:1` (#simple_container_windows_server_qualification_2026-09-27)
- **TODO** Implement and qualify FreeBSD jail-backed Simple Container lifecycle with selected authority and real exit/destroy evidence - `doc/08_tracking/todo/simple_container_freebsd_jail_qualification_2026-09-27.md:1` (#simple_container_freebsd_jail_qualification_2026-09-27)
- **TODO** Repair managed SimpleOS container launch through authenticated loader authority - `doc/08_tracking/bug/simpleos_managed_container_launch_authority_mismatch_2026-09-27.md:1` (#simpleos_managed_container_launch_authority_mismatch_2026-09-27)
- **TODO** Convert src/lib/nogc_sync_mut/sffi/codegen.spl Cranelift module/ISA externs to text-form declarations (compiler text-ABI registry expands them) instead of manual rt_string_data/rt_string_len expansion; isa-feature readback currently receives garbage pointers in seed-built binaries - `src/lib/nogc_sync_mut/sffi/codegen.spl:38` (#codegen_isa_sffi_text_abi_misexpansion_2026_10_22)
- **TODO** Stage-2 bootstrap verification with #5549 trace-scope calls and MIR nil fixes - `doc/08_tracking/todo/test_runner_mcdc_nil_return_followups_2026-10-31.md:35` (##5549)
- **TODO** #5633 HIR NIL-RET-001: rebuild as HIR commits on current release without merges (stale-snapshot-rewind), re-push, dispatch admission - `doc/08_tracking/todo/test_runner_mcdc_nil_return_followups_2026-10-31.md:73` (##5633)
- **TODO** #5646 nil-extern baseline batch draft: release merge (conflicts #5642), guard re-prune, spec rerun - `doc/08_tracking/todo/test_runner_mcdc_nil_return_followups_2026-10-31.md:77` (##5646)
- **TODO** MIR NIL-RET-001 (5 findings): branch never pushed; redo fix from scratch - `doc/08_tracking/todo/test_runner_mcdc_nil_return_followups_2026-10-31.md:79`
- **TODO** Interpreter: T? return arrives as Option::Some(v); typed val, struct field, push and for keep wrapper; fix or lint before more T? signatures - `doc/08_tracking/todo/test_runner_mcdc_nil_return_followups_2026-10-31.md:81`
- **TODO** remove xxh3 dual-run shadow by 2026-11-02 (expiry) once zero mismatches observed across dev/test lanes since landing; then route callers directly to std.common.hash.xxh3 - `src/lib/nogc_sync_mut/hash/xxh3_dual.spl:28`
- **TODO** Run macos_process_live_spec.spl and the Phase2-produced native process-live fixture with absent and present stdbuf after the cold inventory memory blocker is fixed. Source fix and both test forms exist; the first focused compile stopped at 979,808 KiB after 25.4s and produced no artifact. Keep this open until real assertions pass with the admitted Phase2 compiler, recording peak RSS and elapsed time. - `doc/08_tracking/todo/macos_bootstrap_process_live_qualification_2026-09-21.md:3`

## Appendix

### Legend

- **P0/critical:** Blocking, fix immediately
- **P1/high:** Important, next sprint
- **P2/medium:** Should do, backlog
- **P3/low:** Nice to have, someday

### Areas

- `runtime` - GC, values, monoio, concurrency
- `codegen` - MIR, Cranelift, LLVM, Vulkan
- `compiler` - HIR, pipeline, interpreter
- `parser` - Lexer, AST, parsing
- `type` - Type checker, inference
- `stdlib` - Simple standard library
- `gpu` - GPU/SIMD/graphics
- `ui` - UI framework
- `test` - Test frameworks
- `driver` - CLI, tools
- `loader` - SMF loader
- `pkg` - Package manager
- `doc` - Documentation, specs, guides
