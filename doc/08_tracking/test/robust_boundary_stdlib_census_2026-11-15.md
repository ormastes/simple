# Stdlib robust-boundary census baseline (SPL-BOUND-001/002), 2026-11-15

Slice H (stdlib migration) first increment. Produced by
`scripts/census/bound_census.spl` (calls `check_bound_late_casts` and
`check_bound_unit_reasserts`) over the 482 git-tracked `src/lib/**/*.spl`
files that declare an `extern fn` (the only files either detector can flag).

Reproduce: `git ls-files src/lib | grep '\.spl$' | xargs grep -lE '^\s*(pub )?extern fn' > list.txt;
bin/simple run scripts/census/bound_census.spl list.txt`

## Totals (baseline at origin/release/1.0.0)

- files scanned: 482
- SPL-BOUND-001 (raw extern result returned unconverted): 465 findings in 144 files
- SPL-BOUND-002 (late foreign-origin unit cast): 0 (stdlib declares no `unit` types and has no `use unit.` imports)
- SPL-BOUND-reassert: 0

## Re-census 2026-11-16 (SPL-BOUND-001 false-positive correction)

SPL-BOUND-001 now fires only when the extern's declared return is a raw
numeric primitive (`i8..i64`, `u8..u64`, `isize`/`usize`, `f32`/`f64`).
Pass-through of an already-safe extern return (`text?`, `[u8]?`, `Option<..>`,
`Result<..>`, `bool`, `text`, a declared unit, or none) no longer reports.

- files scanned: 486
- SPL-BOUND-001: **249 findings in 93 files** (was 465 in 144)
- The drop of 216 is a false-positive correction in the detector, **not**
  boundary conversions; no library code changed.
- Top areas now: nogc_sync_mut/gpu 44, nogc_sync_mut/io 30, gc_async_mut/gpu 28,
  nogc_sync_mut/gpu_driver 17, common/cache_host_authority_v1.spl 17,
  nogc_async_mut/concurrent 10, common/string_core.spl 9, nogc_sync_mut/jit 7.
  (The baseline tables below are the 2026-11-15 snapshot.)

Most 001 findings are thin forwarders (`fn gpu_memory_alloc(size) -> i64: rt_alloc(size)`),
i.e. a raw extern wrapped without an `@unsafe(capabilities: [ffi])` adapter.

## Findings by area

| area | findings |
|---|---|
| nogc_sync_mut/gpu | 64 |
| nogc_sync_mut/io | 60 |
| gc_async_mut/gpu | 49 |
| common/string_core.spl | 24 |
| nogc_sync_mut/gpu_driver | 19 |
| nogc_sync_mut/jit | 15 |
| nogc_sync_mut/simd_crypto.spl | 14 |
| common/cache_host_authority_v1.spl | 14 |
| other (remaining files) | 206 |

## Per-file counts

- src/lib/common/string_core.spl: 24
- src/lib/nogc_sync_mut/gpu_driver/mod.spl: 19
- src/lib/nogc_sync_mut/simd_crypto.spl: 14
- src/lib/common/cache_host_authority_v1.spl: 14
- src/lib/gc_async_mut/gpu/engine2d/host_gpu_event_queue.spl: 13
- src/lib/nogc_sync_mut/gpu/engine2d/webgpu_sffi.spl: 11
- src/lib/nogc_sync_mut/gpu/engine2d/sffi_intel.spl: 11
- src/lib/nogc_sync_mut/gpu/engine2d/ffi_intel.spl: 11
- src/lib/nogc_async_mut/concurrent/multicore_green.spl: 10
- src/lib/nogc_async_mut/io/mod_stub.spl: 9
- src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_session_runtime_ops.spl: 9
- src/lib/sys/pty.spl: 8
- src/lib/nogc_sync_mut/io/window_sffi.spl: 7
- src/lib/nogc_sync_mut/io/tls_common_hooks.spl: 7
- src/lib/nogc_async_mut/fs/flat.spl: 7
- src/lib/common/encoding/utf8.spl: 7
- src/lib/nogc_sync_mut/io/regex_simple.spl: 6
- src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl: 6
- src/lib/nogc_sync_mut/fs/flat.spl: 6
- src/lib/gc_async_mut/io/regex_simple.spl: 6
- src/lib/common/cache_daemon_host_authority_v1.spl: 6
- src/lib/nogc_sync_mut/tui/terminal.spl: 5
- src/lib/nogc_sync_mut/simd/profile.spl: 5
- src/lib/nogc_sync_mut/mem_tracker/mod.spl: 5
- src/lib/nogc_sync_mut/io/file_ops.spl: 5
- src/lib/nogc_sync_mut/io/dma.spl: 5
- src/lib/nogc_sync_mut/io/dir_entry_ops.spl: 5
- src/lib/nogc_sync_mut/concurrent/thread.spl: 5
- src/lib/nogc_async_mut/thread_pool_state.spl: 5
- src/lib/skia/entity/glyph_outline.spl: 4
- src/lib/nogc_sync_mut/sffi/fs.spl: 4
- src/lib/nogc_sync_mut/ptr/raw.spl: 4
- src/lib/nogc_sync_mut/jit/jit_x86_mixed.spl: 4
- src/lib/nogc_sync_mut/jit/jit_riscv_mixed.spl: 4
- src/lib/nogc_sync_mut/jit/jit_arm_mixed.spl: 4
- src/lib/nogc_sync_mut/database/atomic.spl: 4
- src/lib/log.spl: 4
- src/lib/gc_async_mut/gpu/engine2d/cpu_session.spl: 4
- src/lib/gc_async_mut/gpu/engine2d/backend_cuda_proof.spl: 4
- src/lib/common/text_bytes.spl: 4
- src/lib/common/science_math/perf_sugar.spl: 4
- src/lib/nogc_sync_mut/src/core/random.spl: 3
- src/lib/nogc_sync_mut/src/config.spl: 3
- src/lib/nogc_sync_mut/jit/tiered_jit.spl: 3
- src/lib/nogc_sync_mut/io/process_governor.spl: 3
- src/lib/nogc_sync_mut/io/pipe.spl: 3
- src/lib/nogc_sync_mut/gpu/usm.spl: 3
- src/lib/nogc_sync_mut/gpu/memory.spl: 3
- src/lib/nogc_sync_mut/gpu/engine2d/sffi_rocm.spl: 3
- src/lib/nogc_sync_mut/gpu/engine2d/ffi_rocm.spl: 3
- src/lib/nogc_sync_mut/dual_fs/__init__.spl: 3
- src/lib/nogc_async_mut_noalloc/mimalloc.spl: 3
- src/lib/gc_async_mut/file_system/file_ops.spl: 3
- src/lib/text.spl: 2
- src/lib/scv/compile_source_inventory.spl: 2
- src/lib/nogc_sync_mut/websocket/async_wire_hooks.spl: 2
- src/lib/nogc_sync_mut/src/exp/sweep.spl: 2
- src/lib/nogc_sync_mut/sffi/coverage.spl: 2
- src/lib/nogc_sync_mut/runtime_value.spl: 2
- src/lib/nogc_sync_mut/platform/host_io.spl: 2
- src/lib/nogc_sync_mut/io/time_ops.spl: 2
- src/lib/nogc_sync_mut/io/thread.spl: 2
- src/lib/nogc_sync_mut/io/process_ops.spl: 2
- src/lib/nogc_sync_mut/io/image_sffi.spl: 2
- src/lib/nogc_sync_mut/io/cuda_sffi.spl: 2
- src/lib/nogc_sync_mut/io/coverage_simple.spl: 2
- src/lib/nogc_sync_mut/gpu_profile/mem_profile.spl: 2
- src/lib/nogc_sync_mut/gpu/engine3d/sffi_vulkan3d.spl: 2
- src/lib/nogc_sync_mut/gpu/engine3d/sffi_rocm3d.spl: 2
- src/lib/nogc_sync_mut/gpu/engine3d/sffi_intel3d.spl: 2
- src/lib/nogc_sync_mut/gpu/engine3d/sffi_cuda3d.spl: 2
- src/lib/nogc_sync_mut/gpu/engine2d/simd_native_rows.spl: 2
- src/lib/nogc_sync_mut/ffi/coverage.spl: 2
- src/lib/nogc_sync_mut/enterprise_store/file_backend.spl: 2
- src/lib/nogc_sync_mut/database/core.spl: 2
- src/lib/nogc_sync_mut/dap/hooks.spl: 2
- src/lib/nogc_async_mut_noalloc/tls/transcript.spl: 2
- src/lib/nogc_async_mut/runtime_value.spl: 2
- src/lib/nogc_async_mut/host_io/stdio.spl: 2
- src/lib/nogc_async_mut/dap/hooks.spl: 2
- src/lib/gc_async_mut/runtime_value.spl: 2
- src/lib/gc_async_mut/io/mod_stub.spl: 2
- src/lib/gc_async_mut/gpu/engine2d/render_2d_x86_session.spl: 2
- src/lib/gc_async_mut/gpu/engine2d/backend_opencl.spl: 2
- src/lib/gc_async_mut/gpu/engine2d/backend_metal_runtime_ops.spl: 2
- src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl: 2
- src/lib/gc_async_mut/gpu/browser_engine/script/js_compat.spl: 2
- src/lib/gc_async_mut/gpu/browser_engine/browser_file_ops.spl: 2
- src/lib/gc_async_mut/cuda.spl: 2
- src/lib/common/string_builder.spl: 2
- src/lib/common/science_math/science_math_lib_set_spec.spl: 2
- src/lib/common/crypto/xxhash.spl: 2
- src/lib/sys/terminal_console.spl: 1
- src/lib/nogc_sync_mut/web_framework/asset_pipeline.spl: 1
- src/lib/nogc_sync_mut/text_layout/font_provider.spl: 1
- src/lib/nogc_sync_mut/terminal/relay_terminal.spl: 1
- src/lib/nogc_sync_mut/terminal/power/host_power.spl: 1
- src/lib/nogc_sync_mut/src/exp/storage.spl: 1
- src/lib/nogc_sync_mut/spec/engine_probe.spl: 1
- src/lib/nogc_sync_mut/spec.spl: 1
- src/lib/nogc_sync_mut/runtime/thread_local.spl: 1
- src/lib/nogc_sync_mut/platform.spl: 1
- src/lib/nogc_sync_mut/notebook/lane_locks.spl: 1
- src/lib/nogc_sync_mut/lsp/main_wasi.spl: 1
- src/lib/nogc_sync_mut/io/sysinfo_ops.spl: 1
- src/lib/nogc_sync_mut/io/simple_sdl3.spl: 1
- src/lib/nogc_sync_mut/io/signal_handlers.spl: 1
- src/lib/nogc_sync_mut/io/serial_sffi.spl: 1
- src/lib/nogc_sync_mut/io/profiler_simple.spl: 1
- src/lib/nogc_sync_mut/io/metal_ptr.spl: 1
- src/lib/nogc_sync_mut/io/crypto_sffi.spl: 1
- src/lib/nogc_sync_mut/hooks/stop.spl: 1
- src/lib/nogc_sync_mut/gpu/present_hooks.spl: 1
- src/lib/nogc_sync_mut/gpu/engine2d/sffi_dispatch.spl: 1
- src/lib/nogc_sync_mut/gpu/chromium_reference_oracle_sffi.spl: 1
- src/lib/nogc_sync_mut/engine/audio/ui_click_pcm_raw.spl: 1
- src/lib/nogc_sync_mut/desktop/display.spl: 1
- src/lib/nogc_sync_mut/database/todo.spl: 1
- src/lib/nogc_sync_mut/database/checker.spl: 1
- src/lib/nogc_sync_mut/daemon_sdk/lock.spl: 1
- src/lib/nogc_sync_mut/cuda/sffi.spl: 1
- src/lib/nogc_async_mut/fiber/work_queue.spl: 1
- src/lib/hardware/rv64gc_rtl/fpu.spl: 1
- src/lib/hardware/fpga_linux/synthesis_wrapper.spl: 1
- src/lib/gc_async_mut/gpu_lane/cuda_lane_session.spl: 1
- src/lib/gc_async_mut/gpu/rocm/hip_compute.spl: 1
- src/lib/gc_async_mut/gpu/engine2d/rocm_session.spl: 1
- src/lib/gc_async_mut/gpu/engine2d/opencl_session.spl: 1
- src/lib/gc_async_mut/gpu/engine2d/host_ops.spl: 1
- src/lib/gc_async_mut/gpu/engine2d/backend_cuda_launch_args.spl: 1
- src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl: 1
- src/lib/gc_async_mut/gpu/browser_engine/browser_script_render.spl: 1
- src/lib/gc_async_mut/file_system/permissions.spl: 1
- src/lib/gc_async_mut/cuda/mod.spl: 1
- src/lib/editor/70.backend/gui_sdl_bridge.spl: 1
- src/lib/common/ui/window_scene_draw_ir.spl: 1
- src/lib/common/spec/scenario_helpers.spl: 1
- src/lib/common/simd_scan.spl: 1
- src/lib/common/engine/audio/sound_synth.spl: 1
- src/lib/common/encoding/width_index.spl: 1
- src/lib/common/debug/host_profile_target.spl: 1
- src/lib/common/crypto/xxh3.spl: 1
- src/lib/common/crypto/pbkdf2.spl: 1
- src/lib/common/base_encoding/utilities.spl: 1

## Migration status

No stdlib boundary was migrated to a unit-returning adapter in this increment:
the deployed interpreter cannot construct a unit from a primitive at runtime
(`Unit(x)` -> `function not found`, `x as Unit` -> `cannot cast i64 to Unit`),
so a migrated adapter would break its callers. See
`doc/08_tracking/bug/unit_from_primitive_construction_unsupported_runtime_2026-11-15.md`.
Candidate once that lands: `rt_host_disk_headroom_bytes_v1` in
`src/lib/nogc_sync_mut/io/disk_admission.spl` (one caller, bool-only public surface).
