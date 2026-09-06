# TODO List

**Generated:** 2026-09-06
**Total:** 273 items | **Open:** 270 | **Blocked:** 10 | **Stale:** 0
**Database:** `doc/08_tracking/todo/todo_db.sdn`

## Statistics

### By Area

| Area | Count | P0 | P1 | P2 | P3 | Blocked |
|------|-------|----|----|----|----|---------|
| general | 216 | 0 | 0 | 0 | 216 | 0 |
| gpu | 32 | 0 | 3 | 29 | 0 | 0 |
| debug | 2 | 0 | 0 | 2 | 0 | 0 |
| driver | 1 | 0 | 1 | 0 | 0 | 0 |
| sspec-live-capture | 1 | 0 | 0 | 1 | 0 | 1 |
| sspec-verification | 1 | 0 | 1 | 0 | 0 | 1 |
| llm-caret-messaging | 1 | 0 | 1 | 0 | 0 | 1 |
| sspec | 1 | 0 | 0 | 1 | 0 | 0 |
| infra | 1 | 0 | 0 | 0 | 1 | 0 |
| spipe_docgen | 1 | 0 | 0 | 1 | 0 | 0 |
| test | 2 | 0 | 1 | 1 | 0 | 0 |
| bootstrap | 1 | 0 | 0 | 1 | 0 | 0 |
| uno_q | 1 | 0 | 0 | 1 | 0 | 0 |
| cosmos | 1 | 1 | 0 | 0 | 0 | 0 |
| rendering | 1 | 1 | 0 | 0 | 0 | 0 |
| ui_slim | 7 | 0 | 2 | 2 | 3 | 6 |
| runtime | 1 | 0 | 0 | 1 | 0 | 1 |
| compositor | 1 | 0 | 0 | 1 | 0 | 0 |
| interpreter | 1 | 0 | 0 | 1 | 0 | 0 |

### By Priority

| Priority | Count | Open | Blocked | Stale |
|----------|-------|------|---------|-------|
| P0 (critical) | 2 | 2 | 0 | 0 |
| P1 (high) | 9 | 7 | 4 | 0 |
| P2 (medium) | 42 | 41 | 4 | 0 |
| P3 (low) | 220 | 220 | 2 | 0 |

## P0 - Critical

- **TODO** POSTPONED until identified Cosmos+ hardware and lab fixtures are available: execute and retain BT-001 through BT-006. The 2026-07-29 host audit found a Xilinx ML Carrier FT4232H (`XFL1OSWWFM2B`), a Lauterbach PODBUS controller, and three Samsung NVMe devices, but no Cosmos+/OpenSSD PCIe device. The repo-managed TRACE32 server reached TCP 20000, while read-only CPU, system, and `STATE.RUN()` queries all failed with exit 8128 because no target was configured. - `doc/08_tracking/todo/cosmos_nvme_firmware_remaining_2026-07-28.md:17`
- **TODO** BLOCKED: run the four-lane QEMU/container Vulkan mission showcase with an admitted self-hosted CLI, producer receipts, and an allocation-cap receipt; see TODO DB row 277 and this plan's resume command. - `doc/03_plan/sys_test/render_lane_mission_showcase.md:53`

## P1 - High Priority

- **TODO** `probe` is not a probe. It queries no device: it is a - `src/lib/gc_async_mut/gpu/session/graphics_capabilities.spl:30`
- **TODO** The 15 rt_gpu_session_metal_* / rt_cuda_* / rt_vk_* / rt_webgpu_* - `src/lib/gc_async_mut/gpu/session/backend_runtime_ops.spl:3`
- **TODO** NO Metal device evidence exists on this machine, so no - `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl:75`
- **TODO** Verify Stage 3 self-hosting: the bootstrap has only ever reached 'Stage 2 admitted', and Stage 3 -- stage2 recompiling THIS file -- has never been attempted, so the byte-identical stage2 == stage3 fixpoint that the bootstrap claim rests on is unproven; see doc/08_tracking/bug/bootstrap_stage2_admission_refused_by_concurrent_source_edits_2026-09-05.md - `src/app/cli/bootstrap_main.spl:6`
- **TODO** T1 gate open: all Modern SSpec evidence verified on the Rust bootstrap seed. When a self-hosted binary is deployed, re-run the evidence specs + docgen gate on it - `test/03_system/tools/spipe/examples/live_capture_blocker_sentinels_spec.spl:48`
- **TODO** Run the Phase 4 full-CLI and Caret carrier verification with the exact source-matched candidate after Stage 4 admission; retain binary SHA-256, command outputs, and carrier provenance - `test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl:110`
- **TODO** Re-run every GPU scheduler spec on a redeployed full-CLI pure-Simple binary - `doc/08_tracking/todo/gpu_scheduler_specs_need_selfhosted_rerun_2026-09-06.md:1`
- **TODO** BLOCKED (bootstrap forbidden 2026-09-06): certified H0/T0/T1 startup on a deployed pure-Simple ui binary; seed numbers are diagnostic only - `doc/08_tracking/todo/ui_slim_kernel_plugin_wave3_blocked_2026-09-06.md:9`
- **TODO** BLOCKED: certified G0/G1 window timing on the deployed binary; launcher exit-141 and stale winit marker gate first - `doc/08_tracking/todo/ui_slim_kernel_plugin_wave3_blocked_2026-09-06.md:10`

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
