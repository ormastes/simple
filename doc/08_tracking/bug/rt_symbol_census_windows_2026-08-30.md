# `rt_*` runtime symbol census (Windows host) — 2026-08-30

Read-only measured census of every `rt_*` runtime symbol: DECLARED/referenced
from Simple, DEFINED in the C runtime, DEFINED in the Rust runtime crate.
Nothing in the tree was modified. No bootstrap, no `bin/simple` invocation.

Repo: `C:\Users\ormas\dev\simple`, working tree as of 2026-08-30.

## 1. Scope and method

| axis | scanned | excluded |
|---|---|---|
| C definitions | `src/runtime/**/*.c`, `*.h` | `src/runtime/vendor/**`, `miniaudio.h`, `stb_image.h`, `stb_truetype.h` |
| Rust definitions | `src/compiler_rust/runtime/src/**/*.rs` | — |
| Simple references | `src/lib/**`, `src/compiler/**`, `src/app/**` (`*.spl`) | `vendor/`, whole-line `//`/`#` comments |

A C **definition** = `rt_NAME` followed by balanced parens (possibly
multi-line) then `{`, after comments and string/char literals are stripped, and
after rejecting call-position matches. `static` definitions are recorded
separately: a `static` function is TU-local and **cannot back a Simple
`extern`**, so it is excluded from the "defined in C" set.

A Rust **definition** = `pub [unsafe] [extern "C"] fn rt_NAME`. `#[cfg(...)]`
attributes are captured only from the contiguous attribute block immediately
preceding the `fn` line. `#[cfg(test)]` items and `*_test` helpers are excluded.

**C and Rust defined-sets are never unioned into one "is it defined" answer.**
They are parallel implementations; `.claude/rules/vcs.md` records that unioning
them masked real Rust-only removals.

## 2. Bucket counts

| bucket | count |
|---|---|
| defined in **BOTH** C and Rust | 560 |
| defined in **C only** | 714 |
| defined in **Rust only** | 1454 |
| **defined union** (C non-static or Rust non-test) | 2728 |
| referenced from Simple (`extern fn` or call site) | 2417 |
| of which `extern fn` declarations | 2272 |
| **referenced but defined in NEITHER** | **1114** |
| defined but never referenced from Simple | 1425 |

Supporting counts:

| | count |
|---|---|
| C `rt_*` definitions found (incl. `static`) | 1542 |
| ... of which `static`-only (cannot back an extern) | 268 |
| C `#define rt_*` macro definitions | 2 |
| Rust `rt_*` definitions found (incl. test-only) | 2016 |

Cross-check against the repo's own push guard
(`scripts/check/check-runtime-api-regression-push.shs`, which reported
**2821 symbols** on 2026-08-23): that guard's coarser regexes yield 1508 C +
1804 Rust here. This census's extractor is a strict superset of both (it also
catches multi-line signatures, indented definitions and `pub unsafe extern`),
so the NEITHER bucket below is **conservative** — a looser extractor would
report more gaps, not fewer.

**Do not read 2728 < 2821 as a contradiction.** The three numbers count
different things. The guard's C regex `^[A-Za-z_][A-Za-z0-9_ \*]*...` matches
`static` definitions too (its very first hit here is
`static int rt_msvc_ftruncate`), and it unions C with Rust into one set; 2821
was also measured on a different checkout (2026-08-23). This census's 2728 is
*post*-filter: 268 `static`-only and 2 test-only symbols are deliberately
removed, because neither can back a Simple `extern`. The superset claim applies
to the raw extraction (1542 >= 1508 C, 2016 >= 1804 Rust), not to the filtered
union.

## 3. The critical bucket: referenced but defined in NEITHER (1114)

These `rt_*` symbols are declared `extern fn` or called from Simple source, and
have **no non-`static` C definition and no non-test Rust runtime definition**.
This is the same defect class as
`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md` (an unbacked
extern returns nil silently) and the `rt_unwrap_or_trap` NULL-GOT SIGSEGV in
`doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`.
Magnitude is consistent with the 1,466 unbacked externs already recorded in
`.claude/rules/vcs.md`.

The bucket splits in two:

| sub-bucket | count | meaning |
|---|---|---|
| **3a. interpreter-only** | 405 | named somewhere in `src/compiler_rust/**` outside the runtime crate (interpreter extern dispatch, codegen tables, capability-gap lists). Works under the interpreter; **undefined at native link time on every platform, Windows included.** |
| **3b. defined nowhere at all** | 709 | not named anywhere in `src/compiler_rust/**` either. No backing on any path. |

### 3b family breakdown (top prefixes)

| prefix | count |
|---|---|
| `rt_torch_*` | 112 |
| `rt_lyon_*` | 47 |
| `rt_debug_*` | 40 |
| `rt_cuda_*` | 31 |
| `rt_ftp_*` | 25 |
| `rt_vk_*` | 24 |
| `rt_gamepad_*` | 19 |
| `rt_http_*` | 15 |
| `rt_value_*` | 15 |
| `rt_hook_*` | 14 |
| `rt_quic_*` | 14 |
| `rt_exec_*` | 13 |
| `rt_ssh_*` | 13 |
| `rt_metal_*` | 12 |
| `rt_wgpu_*` | 11 |
| `rt_intel_*` | 10 |
| `rt_oneapi_*` | 10 |
| `rt_sftp_*` | 10 |
| `rt_time_*` | 10 |
| `rt_riscv64_*` | 9 |
| `rt_get_*` | 8 |
| `rt_ptrace_*` | 8 |
| `rt_tar_*` | 8 |
| `rt_volatile_*` | 8 |
| `rt_zip_*` | 8 |
| `rt_cpu_*` | 7 |
| `rt_dma_*` | 7 |
| `rt_dwarf_*` | 6 |
| `rt_engine2d_*` | 6 |
| `rt_simd_*` | 6 |

### 3b. Full list — referenced, defined nowhere (709)

| symbol | first reference |
|---|---|
| `rt_aes_gcm_decrypt_hex` | `extern @ src/lib/nogc_async_mut/io/quic/quic_crypto.spl:31` |
| `rt_aes_gcm_encrypt_hex` | `extern @ src/lib/nogc_async_mut/io/quic/quic_crypto.spl:30` |
| `rt_alloc_exec_memory` | `extern @ src/compiler/90.tools/sffi_gen/specs/exec_memory.spl:34` |
| `rt_alloc_rw_memory` | `extern @ src/compiler/90.tools/sffi_gen/specs/exec_memory.spl:90` |
| `rt_array_get_operand` | `call @ src/compiler/50.mir/_MirLoweringExpr/literals.spl:277` |
| `rt_array_len_operand` | `call @ src/compiler/50.mir/_MirLoweringExpr/literals.spl:271` |
| `rt_array_push_operand` | `call @ src/compiler/50.mir/_MirLoweringExpr/literals.spl:283` |
| `rt_bdd_executed_count` | `extern @ src/lib/nogc_sync_mut/test_runner/test_result_wrapper.spl:462` |
| `rt_build_symbol_table` | `extern @ src/compiler/90.tools/sffi_gen/specs/compiler_query.spl:140` |
| `rt_call_function_0` | `extern @ src/compiler/90.tools/sffi_gen/specs/exec_memory.spl:129` |
| `rt_call_function_1` | `extern @ src/compiler/90.tools/sffi_gen/specs/exec_memory.spl:139` |
| `rt_call_function_2` | `extern @ src/compiler/90.tools/sffi_gen/specs/exec_memory.spl:150` |
| `rt_cli_args` | `extern @ src/app/dashboard/web_entry.spl:14` |
| `rt_cli_run_ffi_gen` | `extern @ src/lib/nogc_sync_mut/ffi/cli.spl:179` |
| `rt_command_output` | `extern @ src/lib/nogc_sync_mut/baremetal/transport/dedicated_hw.spl:13` |
| `rt_coverage_path_finalizer` | `extern @ src/lib/nogc_sync_mut/io/coverage_simple.spl:21` |
| `rt_cpu_arch_name` | `extern @ src/lib/gc_async_mut/gpu/engine2d/host_ops.spl:5` |
| `rt_cpu_count` | `extern @ src/lib/nogc_sync_mut/sffi/system.spl:179` |
| `rt_cpu_has_avx2` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/simd_kernels3d.spl:40` |
| `rt_cpu_has_avx512` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/simd_kernels3d.spl:41` |
| `rt_cpu_has_neon` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/simd_kernels3d.spl:42` |
| `rt_cpu_has_sse42` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/simd_kernels3d.spl:39` |
| `rt_cpu_present_pixels` | `extern @ src/lib/nogc_sync_mut/gpu/present_hooks.spl:3` |
| `rt_cuda3d_available` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/ffi_cuda3d.spl:22` |
| `rt_cuda3d_init` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/ffi_cuda3d.spl:23` |
| `rt_cuda3d_shutdown` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/ffi_cuda3d.spl:24` |
| `rt_cuda_alloc_device` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/cuda_session.spl:26` |
| `rt_cuda_alloc_fb` | `extern @ src/lib/gc_async_mut/gpu/engine2d/backend_cuda_proof.spl:16` |
| `rt_cuda_cleanup` | `extern @ src/lib/gc_async_mut/gpu/engine2d/backend_cuda_proof.spl:20` |
| `rt_cuda_clear` | `extern @ src/lib/gc_async_mut/gpu/engine2d/backend_cuda_proof.spl:17` |
| `rt_cuda_compile_ptx` | `extern @ src/lib/nogc_async_mut/engine/physics/backend_gpu/gpu_solver.spl:27` |
| `rt_cuda_compute_capability` | `extern @ src/lib/nogc_sync_mut/io/cuda_sffi.spl:16` |
| `rt_cuda_device_init` | `extern @ src/lib/gc_async_mut/gpu/engine2d/backend_cuda_proof.spl:15` |
| `rt_cuda_device_memory` | `extern @ src/lib/nogc_sync_mut/io/cuda_sffi.spl:15` |
| `rt_cuda_draw_rect` | `extern @ src/lib/gc_async_mut/gpu/engine2d/backend_cuda_proof.spl:18` |
| `rt_cuda_get_device` | `extern @ src/lib/nogc_sync_mut/io/cuda_sffi.spl:13` |
| `rt_cuda_get_function` | `extern @ src/lib/nogc_async_mut/engine/physics/backend_gpu/gpu_solver.spl:28` |
| `rt_cuda_get_last_error` | `extern @ src/lib/nogc_sync_mut/io/cuda_sffi.spl:32` |
| `rt_cuda_host_alloc` | `call @ src/lib/nogc_sync_mut/gpu/usm.spl:16` |
| `rt_cuda_kernel_get` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/cuda_session.spl:24` |
| `rt_cuda_kernel_launch` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/cuda_session.spl:25` |
| `rt_cuda_memcpy_d2d` | `extern @ src/lib/nogc_sync_mut/io/cuda_sffi.spl:22` |
| `rt_cuda_memcpy_d2h` | `extern @ src/lib/nogc_async_mut/engine/physics/backend_gpu/gpu_solver.spl:25` |
| `rt_cuda_memcpy_h2d` | `extern @ src/lib/nogc_async_mut/engine/physics/backend_gpu/gpu_solver.spl:24` |
| `rt_cuda_peek_last_error` | `extern @ src/lib/nogc_sync_mut/io/cuda_sffi.spl:33` |
| `rt_cuda_primary_ctx_release` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/cuda_session.spl:22` |
| `rt_cuda_primary_ctx_retain` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/cuda_session.spl:21` |
| `rt_cuda_readback` | `extern @ src/lib/gc_async_mut/gpu/engine2d/backend_cuda_proof.spl:19` |
| `rt_cuda_set_device` | `extern @ src/lib/nogc_sync_mut/io/cuda_sffi.spl:12` |
| `rt_cuda_shutdown` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/ffi_cuda.spl:24` |
| `rt_cuda_sm_version` | `extern @ src/compiler/30.types/simd_capabilities.spl:46` |
| `rt_cuda_stream_create` | `extern @ src/lib/nogc_async_mut/engine/physics/backend_gpu/gpu_solver.spl:32` |
| `rt_cuda_stream_destroy` | `extern @ src/lib/nogc_async_mut/engine/physics/backend_gpu/gpu_solver.spl:33` |
| `rt_cuda_stream_sync` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/cuda_session.spl:28` |
| `rt_cuda_stream_synchronize` | `extern @ src/lib/nogc_sync_mut/io/cuda_sffi.spl:31` |
| `rt_cuda_submit` | `extern @ src/lib/gc_async_mut/gpu/session/backend_runtime_ops.spl:7` |
| `rt_cuda_unload_module` | `extern @ src/lib/nogc_async_mut/engine/physics/backend_gpu/gpu_solver.spl:30` |
| `rt_debug_add_breakpoint_at` | `call @ src/lib/nogc_async_mut/mcp/debug_handlers.spl:92` |
| `rt_debug_add_breakpoint_rich` | `call @ src/lib/nogc_sync_mut/io/debug_stubs.spl:60` |
| `rt_debug_add_function_breakpoint` | `call @ src/lib/nogc_async_mut/mcp/debug_handlers.spl:299` |
| `rt_debug_add_watch` | `call @ src/lib/nogc_async_mut/mcp/debug_handlers.spl:385` |
| `rt_debug_clear_breakpoints` | `extern @ src/lib/nogc_sync_mut/ffi/debug.spl:77` |
| `rt_debug_clear_globals` | `extern @ src/lib/nogc_sync_mut/ffi/debug.spl:125` |
| `rt_debug_clear_locals` | `extern @ src/lib/nogc_sync_mut/ffi/debug.spl:124` |
| `rt_debug_continue_exec` | `call @ src/lib/nogc_async_mut/mcp/debug_handlers.spl:143` |
| `rt_debug_current_column` | `extern @ src/lib/nogc_sync_mut/ffi/debug.spl:59` |
| `rt_debug_eval_expression` | `call @ src/lib/nogc_sync_mut/io/debug_stubs.spl:104` |
| `rt_debug_frame_locals` | `call @ src/lib/nogc_sync_mut/io/debug_stubs.spl:82` |
| `rt_debug_get_breakpoint_info` | `call @ src/lib/nogc_sync_mut/io/debug_stubs.spl:69` |
| `rt_debug_get_current_file` | `call @ src/lib/nogc_async_mut/mcp/debug_handlers.spl:221` |
| `rt_debug_get_current_line` | `call @ src/lib/nogc_async_mut/mcp/debug_handlers.spl:222` |
| `rt_debug_get_selected_frame` | `call @ src/lib/nogc_sync_mut/io/debug_stubs.spl:79` |
| `rt_debug_get_source_lines` | `call @ src/lib/nogc_async_mut/mcp/debug_handlers.spl:362` |
| `rt_debug_get_step_mode` | `extern @ src/lib/nogc_sync_mut/ffi/debug.spl:13` |
| `rt_debug_get_step_start_depth` | `extern @ src/lib/nogc_sync_mut/ffi/debug.spl:15` |
| `rt_debug_globals` | `extern @ src/lib/nogc_sync_mut/ffi/debug.spl:123` |
| `rt_debug_has_breakpoint` | `extern @ src/lib/nogc_sync_mut/ffi/debug.spl:78` |
| `rt_debug_is_paused` | `extern @ src/lib/nogc_sync_mut/ffi/debug.spl:39` |
| `rt_debug_list_watches` | `call @ src/lib/nogc_async_mut/mcp/debug_handlers.spl:410` |
| `rt_debug_local_vars` | `call @ src/lib/nogc_async_mut/mcp/debug_handlers.spl:183` |
| `rt_debug_pause_exec` | `call @ src/lib/nogc_sync_mut/io/debug_stubs.spl:41` |
| `rt_debug_pop_frame` | `extern @ src/lib/nogc_sync_mut/ffi/debug.spl:102` |
| `rt_debug_push_frame` | `extern @ src/lib/nogc_sync_mut/ffi/debug.spl:101` |
| `rt_debug_remove_breakpoint_at` | `call @ src/lib/nogc_async_mut/mcp/debug_handlers.spl:124` |
| `rt_debug_remove_watch` | `call @ src/lib/nogc_async_mut/mcp/debug_handlers.spl:399` |
| `rt_debug_select_frame` | `call @ src/lib/nogc_sync_mut/io/debug_stubs.spl:76` |
| `rt_debug_set_breakpoint_enabled` | `call @ src/lib/nogc_async_mut/mcp/debug_handlers.spl:330` |
| `rt_debug_set_current_location` | `extern @ src/lib/nogc_sync_mut/ffi/debug.spl:56` |
| `rt_debug_set_global` | `extern @ src/lib/nogc_sync_mut/ffi/debug.spl:121` |
| `rt_debug_set_local` | `extern @ src/lib/nogc_sync_mut/ffi/debug.spl:120` |
| `rt_debug_set_step_mode_val` | `call @ src/lib/nogc_async_mut/mcp/debug_handlers.spl:165` |
| `rt_debug_set_step_start_depth` | `extern @ src/lib/nogc_sync_mut/ffi/debug.spl:14` |
| `rt_debug_set_variable` | `call @ src/lib/nogc_async_mut/mcp/debug_handlers.spl:440` |
| `rt_debug_should_break` | `extern @ src/lib/nogc_sync_mut/ffi/debug.spl:94` |
| `rt_debug_stack_trace_lines` | `call @ src/lib/nogc_async_mut/mcp/debug_handlers.spl:208` |
| `rt_debug_terminate` | `call @ src/lib/nogc_async_mut/mcp/debug_handlers.spl:578` |
| `rt_debug_wait_for_continue` | `extern @ src/lib/nogc_sync_mut/ffi/debug.spl:40` |
| `rt_decrypt_aes256` | `extern @ src/lib/nogc_sync_mut/io/crypto_sffi.spl:36` |
| `rt_deflate_compress` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:20` |
| `rt_deflate_decompress` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:21` |
| `rt_derive_key_pbkdf2` | `extern @ src/lib/nogc_sync_mut/io/crypto_sffi.spl:45` |
| `rt_dma_alloc__fallback` | `call @ src/lib/nogc_sync_mut/io/dma.spl:220` |
| `rt_dma_cache_line_size__fallback` | `call @ src/lib/nogc_sync_mut/io/dma.spl:241` |
| `rt_dma_free__fallback` | `call @ src/lib/nogc_sync_mut/io/dma.spl:226` |
| `rt_dma_phys_of__fallback` | `call @ src/lib/nogc_sync_mut/io/dma.spl:234` |
| `rt_dma_sync_for_cpu__fallback` | `call @ src/lib/nogc_sync_mut/io/dma.spl:239` |
| `rt_dma_sync_for_device__fallback` | `call @ src/lib/nogc_sync_mut/io/dma.spl:238` |
| `rt_dma_virt_of__fallback` | `call @ src/lib/nogc_sync_mut/io/dma.spl:229` |
| `rt_dwarf_addr_to_line` | `extern @ src/lib/nogc_sync_mut/debug/native_agent.spl:22` |
| `rt_dwarf_free` | `extern @ src/lib/nogc_sync_mut/debug/native_agent.spl:21` |
| `rt_dwarf_function_at` | `extern @ src/lib/nogc_sync_mut/debug/native_agent.spl:23` |
| `rt_dwarf_line_to_addr` | `extern @ src/lib/nogc_sync_mut/debug/native_agent.spl:25` |
| `rt_dwarf_load` | `extern @ src/lib/nogc_sync_mut/debug/native_agent.spl:20` |
| `rt_dwarf_locals_at` | `extern @ src/lib/nogc_sync_mut/debug/native_agent.spl:24` |
| `rt_ecdsa_p384_sign` | `extern @ src/lib/nogc_sync_mut/io/signature_sffi.spl:103` |
| `rt_ecdsa_p384_verify` | `extern @ src/lib/nogc_sync_mut/io/signature_sffi.spl:98` |
| `rt_ecdsa_p521_sign` | `extern @ src/lib/nogc_sync_mut/io/signature_sffi.spl:115` |
| `rt_ecdsa_p521_verify` | `extern @ src/lib/nogc_sync_mut/io/signature_sffi.spl:108` |
| `rt_encrypt_aes256` | `extern @ src/lib/nogc_sync_mut/io/crypto_sffi.spl:35` |
| `rt_engine2d_download_pixels` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/ffi_cuda.spl:41` |
| `rt_engine2d_pack_args_4` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/ffi_cuda.spl:38` |
| `rt_engine2d_pack_args_8` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/ffi_cuda.spl:39` |
| `rt_engine2d_simd_row_probe` | `call @ src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl:188` |
| `rt_engine2d_upload_host_buf` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/ffi_cuda.spl:42` |
| `rt_engine2d_upload_pixels` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/ffi_cuda.spl:40` |
| `rt_ensure_dir` | `extern @ src/lib/nogc_sync_mut/terminal/credential/store.spl:450` |
| `rt_entropy_fill` | `extern @ src/lib/nogc_sync_mut/crypto/entropy_platform.spl:7` |
| `rt_env_get_home` | `extern @ src/lib/nogc_sync_mut/terminal/credential/store.spl:167` |
| `rt_eprint` | `call @ src/compiler/70.backend/backend/llvm_backend.spl:468` |
| `rt_exec_manager_backend_name` | `call @ src/compiler/95.interp/execution/mod.spl:90` |
| `rt_exec_manager_compile` | `call @ src/compiler/95.interp/execution/mod.spl:73` |
| `rt_exec_manager_compile_file` | `call @ src/app/io/jit_ffi.spl:110` |
| `rt_exec_manager_compile_mir` | `call @ src/app/io/jit_ffi.spl:107` |
| `rt_exec_manager_compile_source` | `call @ src/app/io/jit_ffi.spl:97` |
| `rt_exec_manager_execute_void` | `call @ src/app/io/jit_ffi.spl:173` |
| `rt_exec_manager_get_opt_level` | `call @ src/app/io/jit_ffi.spl:216` |
| `rt_exec_manager_is_valid` | `call @ src/app/io/jit_ffi.spl:210` |
| `rt_exec_manager_list_functions` | `call @ src/app/io/jit_ffi.spl:200` |
| `rt_exec_manager_set_opt_level` | `call @ src/app/io/jit_ffi.spl:213` |
| `rt_exec_memory_count` | `extern @ src/compiler/90.tools/sffi_gen/specs/exec_memory.spl:209` |
| `rt_exec_memory_dump_stats` | `extern @ src/compiler/90.tools/sffi_gen/specs/exec_memory.spl:215` |
| `rt_exec_memory_total` | `extern @ src/compiler/90.tools/sffi_gen/specs/exec_memory.spl:201` |
| `rt_extract_all_symbols` | `extern @ src/compiler/90.tools/sffi_gen/specs/compiler_query.spl:180` |
| `rt_extract_all_symbols_v2` | `extern @ src/compiler/90.tools/sffi_gen/specs/compiler_query.spl:181` |
| `rt_file_modified` | `extern @ src/lib/nogc_sync_mut/sffi/io.spl:20` |
| `rt_file_read` | `extern @ src/lib/nogc_sync_mut/coverage.spl:12` |
| `rt_file_set_mode` | `extern @ src/lib/gc_async_mut/file_system/permissions.spl:6` |
| `rt_file_write_bytes_b64` | `extern @ src/lib/nogc_sync_mut/play/page.spl:15` |
| `rt_find_symbol_at_position` | `extern @ src/compiler/90.tools/sffi_gen/specs/compiler_query.spl:150` |
| `rt_find_symbol_at_position_v2` | `extern @ src/compiler/90.tools/sffi_gen/specs/compiler_query.spl:151` |
| `rt_find_symbol_references` | `extern @ src/compiler/90.tools/sffi_gen/specs/compiler_query.spl:160` |
| `rt_flush_icache` | `extern @ src/compiler/90.tools/sffi_gen/specs/exec_memory.spl:101` |
| `rt_font_find_table` | `extern @ src/lib/skia/entity/glyph_outline.spl:85` |
| `rt_font_read_i16` | `extern @ src/lib/skia/entity/glyph_outline.spl:78` |
| `rt_font_read_u16` | `extern @ src/lib/skia/entity/glyph_outline.spl:75` |
| `rt_font_read_u32` | `extern @ src/lib/skia/entity/glyph_outline.spl:81` |
| `rt_fork_parent_stderr` | `extern @ src/lib/nogc_sync_mut/test_runner/test_runner_fork.spl:40` |
| `rt_free_ast` | `extern @ src/compiler/90.tools/sffi_gen/specs/compiler_query.spl:208` |
| `rt_free_exec_memory` | `extern @ src/compiler/90.tools/sffi_gen/specs/exec_memory.spl:46` |
| `rt_free_symbol_table` | `extern @ src/compiler/90.tools/sffi_gen/specs/compiler_query.spl:217` |
| `rt_ftp_append` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:36` |
| `rt_ftp_cdup` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:27` |
| `rt_ftp_connect` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:17` |
| `rt_ftp_connect_secure` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:18` |
| `rt_ftp_cwd` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:26` |
| `rt_ftp_delete` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:37` |
| `rt_ftp_disconnect` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:20` |
| `rt_ftp_get` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:34` |
| `rt_ftp_get_welcome_msg` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:52` |
| `rt_ftp_is_connected` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:53` |
| `rt_ftp_list` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:30` |
| `rt_ftp_login` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:19` |
| `rt_ftp_mdtm` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:40` |
| `rt_ftp_mkdir` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:28` |
| `rt_ftp_noop` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:51` |
| `rt_ftp_put` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:35` |
| `rt_ftp_pwd` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:25` |
| `rt_ftp_quit` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:21` |
| `rt_ftp_rename` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:38` |
| `rt_ftp_rmdir` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:29` |
| `rt_ftp_set_mode_active` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:45` |
| `rt_ftp_set_mode_passive` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:44` |
| `rt_ftp_set_transfer_type_ascii` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:47` |
| `rt_ftp_set_transfer_type_binary` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:46` |
| `rt_ftp_size` | `extern @ src/lib/nogc_sync_mut/io/ftp_sffi.spl:39` |
| `rt_gamepad_axis_data` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:37` |
| `rt_gamepad_button_data` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:34` |
| `rt_gamepad_button_is_pressed` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:33` |
| `rt_gamepad_event_free` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:25` |
| `rt_gamepad_event_get_axis` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:29` |
| `rt_gamepad_event_get_button` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:28` |
| `rt_gamepad_event_get_gamepad_id` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:27` |
| `rt_gamepad_event_get_type` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:26` |
| `rt_gamepad_event_get_value` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:30` |
| `rt_gamepad_get_last_error` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:44` |
| `rt_gamepad_get_name` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:20` |
| `rt_gamepad_get_power_info` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:21` |
| `rt_gamepad_init` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:13` |
| `rt_gamepad_is_connected` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:19` |
| `rt_gamepad_poll_event` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:24` |
| `rt_gamepad_set_rumble` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:40` |
| `rt_gamepad_shutdown` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:14` |
| `rt_gamepad_stop_rumble` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:41` |
| `rt_gamepad_update` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:15` |
| `rt_gc_init` | `extern @ src/lib/nogc_sync_mut/ffi/runtime.spl:8` |
| `rt_gc_malloc` | `extern @ src/lib/nogc_sync_mut/ffi/runtime.spl:18` |
| `rt_gc_malloc_atomic` | `call @ src/compiler/90.tools/sffi_gen/specs/gc_full.spl:122` |
| `rt_generate_key` | `extern @ src/lib/nogc_sync_mut/io/crypto_sffi.spl:40` |
| `rt_generate_key_hex` | `extern @ src/lib/nogc_sync_mut/io/crypto_sffi.spl:41` |
| `rt_get_context_keywords` | `extern @ src/compiler/90.tools/sffi_gen/specs/compiler_query.spl:199` |
| `rt_get_file_mtime` | `extern @ src/compiler/90.tools/sffi_gen/specs/compiler_query.spl:131` |
| `rt_get_function_pointer` | `extern @ src/compiler/90.tools/sffi_gen/specs/exec_memory.spl:117` |
| `rt_get_jit_backend` | `call @ src/compiler/95.interp/execution/mod.spl:106` |
| `rt_get_page_size` | `extern @ src/compiler/90.tools/sffi_gen/specs/mmap.spl:83` |
| `rt_get_protection` | `extern @ src/compiler/90.tools/sffi_gen/specs/exec_memory.spl:176` |
| `rt_get_scope_at_position` | `extern @ src/compiler/90.tools/sffi_gen/specs/compiler_query.spl:170` |
| `rt_get_scope_at_position_v2` | `extern @ src/compiler/90.tools/sffi_gen/specs/compiler_query.spl:171` |
| `rt_getauxval` | `extern @ src/compiler/30.types/simd_capabilities.spl:23` |
| `rt_getenv` | `call @ src/compiler/70.backend/backend/llvm_backend.spl:412` |
| `rt_ghdl_verify_return_zero_contract` | `extern @ src/lib/hardware/riscv_common/core/riscv_formal.spl:14` |
| `rt_ghdl_verify_vhdl_constraints` | `extern @ src/lib/hardware/riscv_common/core/riscv_formal.spl:13` |
| `rt_gui_present_html` | `extern @ src/app/editor/gui_shell.spl:14` |
| `rt_gzip_compress` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:13` |
| `rt_gzip_compress_file` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:15` |
| `rt_gzip_decompress` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:14` |
| `rt_gzip_decompress_file` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:16` |
| `rt_hash_blake3` | `extern @ src/lib/nogc_sync_mut/io/crypto_sffi.spl:16` |
| `rt_hash_sha256` | `extern @ src/lib/nogc_sync_mut/io/crypto_sffi.spl:13` |
| `rt_hash_sha3_256` | `extern @ src/lib/nogc_sync_mut/io/crypto_sffi.spl:15` |
| `rt_hash_sha512` | `extern @ src/lib/nogc_sync_mut/io/crypto_sffi.spl:14` |
| `rt_hex` | `call @ src/lib/nogc_sync_mut/debug/remote/protocol/openocd.spl:63` |
| `rt_hex_to_wire` | `extern @ src/lib/nogc_sync_mut/io/tls_common_hooks.spl:8` |
| `rt_hmac_sha256` | `extern @ src/lib/nogc_sync_mut/io/crypto_sffi.spl:20` |
| `rt_hmac_sha512` | `extern @ src/lib/nogc_sync_mut/io/crypto_sffi.spl:21` |
| `rt_hook_add_breakpoint` | `extern @ src/lib/nogc_async_mut/dap/hooks.spl:517` |
| `rt_hook_continue` | `extern @ src/lib/nogc_async_mut/dap/hooks.spl:520` |
| `rt_hook_disable_debugging` | `extern @ src/lib/nogc_async_mut/dap/hooks.spl:530` |
| `rt_hook_enable_debugging` | `extern @ src/lib/nogc_async_mut/dap/hooks.spl:529` |
| `rt_hook_evaluate_condition` | `extern @ src/lib/nogc_async_mut/dap/hooks.spl:528` |
| `rt_hook_evaluate_expression` | `extern @ src/lib/nogc_async_mut/dap/hooks.spl:527` |
| `rt_hook_get_call_depth` | `extern @ src/lib/nogc_async_mut/dap/hooks.spl:524` |
| `rt_hook_get_stack_frames` | `extern @ src/lib/nogc_async_mut/dap/hooks.spl:525` |
| `rt_hook_get_variables` | `extern @ src/lib/nogc_async_mut/dap/hooks.spl:526` |
| `rt_hook_pause` | `extern @ src/lib/nogc_async_mut/dap/hooks.spl:521` |
| `rt_hook_remove_breakpoint` | `extern @ src/lib/nogc_async_mut/dap/hooks.spl:518` |
| `rt_hook_set_breakpoint_enabled` | `extern @ src/lib/nogc_async_mut/dap/hooks.spl:519` |
| `rt_hook_step` | `extern @ src/lib/nogc_async_mut/dap/hooks.spl:522` |
| `rt_hook_terminate` | `extern @ src/lib/nogc_async_mut/dap/hooks.spl:523` |
| `rt_host_gpu_active_backend_handle` | `extern @ src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl:22` |
| `rt_http_client_set_header` | `extern @ src/lib/nogc_sync_mut/io/http_sffi.spl:43` |
| `rt_http_delete` | `extern @ src/lib/nogc_sync_mut/io/http_sffi.spl:21` |
| `rt_http_head` | `extern @ src/lib/nogc_sync_mut/io/http_sffi.spl:23` |
| `rt_http_patch` | `extern @ src/lib/nogc_sync_mut/io/http_sffi.spl:22` |
| `rt_http_post` | `extern @ src/lib/nogc_sync_mut/io/http_sffi.spl:19` |
| `rt_http_put` | `extern @ src/lib/nogc_sync_mut/io/http_sffi.spl:20` |
| `rt_http_server_create` | `extern @ src/lib/nogc_sync_mut/io/http_sffi.spl:55` |
| `rt_http_server_destroy` | `extern @ src/lib/nogc_sync_mut/io/http_sffi.spl:60` |
| `rt_http_server_route` | `extern @ src/lib/nogc_sync_mut/io/http_sffi.spl:56` |
| `rt_http_server_start` | `extern @ src/lib/nogc_sync_mut/io/http_sffi.spl:58` |
| `rt_http_server_static` | `extern @ src/lib/nogc_sync_mut/io/http_sffi.spl:57` |
| `rt_http_server_stop` | `extern @ src/lib/nogc_sync_mut/io/http_sffi.spl:59` |
| `rt_http_upload` | `extern @ src/lib/nogc_sync_mut/io/http_sffi.spl:37` |
| `rt_http_url_decode` | `extern @ src/lib/nogc_sync_mut/io/http_sffi.spl:76` |
| `rt_http_url_encode` | `extern @ src/lib/nogc_sync_mut/io/http_sffi.spl:75` |
| `rt_init_signal_handlers` | `extern @ src/app/interpreter/core/execution_guard.spl:64` |
| `rt_intel3d_available` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/ffi_intel3d.spl:19` |
| `rt_intel3d_init` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/ffi_intel3d.spl:20` |
| `rt_intel3d_shutdown` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/ffi_intel3d.spl:21` |
| `rt_intel_command_list_create` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/ffi_intel.spl:28` |
| `rt_intel_device_count` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/ffi_intel.spl:27` |
| `rt_intel_driver_count` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/ffi_intel.spl:26` |
| `rt_intel_init` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/ffi_intel.spl:23` |
| `rt_intel_is_available` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/ffi_intel.spl:25` |
| `rt_intel_kernel_create` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/ffi_intel.spl:29` |
| `rt_intel_launch_kernel` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/ffi_intel.spl:30` |
| `rt_intel_mem_alloc` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/ffi_intel.spl:31` |
| `rt_intel_mem_free` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/ffi_intel.spl:32` |
| `rt_intel_shutdown` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/ffi_intel.spl:24` |
| `rt_is_darwin_arm64` | `extern @ src/compiler/30.types/simd_capabilities.spl:26` |
| `rt_is_executable` | `extern @ src/compiler/90.tools/sffi_gen/specs/exec_memory.spl:165` |
| `rt_list_dir` | `extern @ src/compiler/35.semantics/lint/remote_exec_lint.spl:534` |
| `rt_list_dir_recursive` | `extern @ src/lib/nogc_sync_mut/sffi/io.spl:208` |
| `rt_load_barrier__fallback` | `call @ src/lib/nogc_sync_mut/io/volatile_ops.spl:63` |
| `rt_lyon_fill_tessellate_with_rule` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:39` |
| `rt_lyon_fill_tessellation_get_indices` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:42` |
| `rt_lyon_fill_tessellation_get_vertices` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:41` |
| `rt_lyon_fill_tessellation_index_count` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:44` |
| `rt_lyon_fill_tessellation_vertex_count` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:43` |
| `rt_lyon_get_last_error` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:77` |
| `rt_lyon_index_buffer_free` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:63` |
| `rt_lyon_index_buffer_get` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:64` |
| `rt_lyon_index_buffer_size` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:65` |
| `rt_lyon_index_buffer_to_array` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:66` |
| `rt_lyon_path_builder_arc_to` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:19` |
| `rt_lyon_path_builder_begin` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:15` |
| `rt_lyon_path_builder_build` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:21` |
| `rt_lyon_path_builder_close` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:20` |
| `rt_lyon_path_builder_cubic_bezier_to` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:18` |
| `rt_lyon_path_builder_free` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:14` |
| `rt_lyon_path_builder_line_to` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:16` |
| `rt_lyon_path_builder_new` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:13` |
| `rt_lyon_path_builder_quadratic_bezier_to` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:17` |
| `rt_lyon_path_circle` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:32` |
| `rt_lyon_path_contains_point` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:26` |
| `rt_lyon_path_ellipse` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:33` |
| `rt_lyon_path_free` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:24` |
| `rt_lyon_path_get_bounds` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:25` |
| `rt_lyon_path_polygon` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:34` |
| `rt_lyon_path_rectangle` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:30` |
| `rt_lyon_path_rounded_rectangle` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:31` |
| `rt_lyon_path_star` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:35` |
| `rt_lyon_path_transform` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:27` |
| `rt_lyon_stroke_tessellate` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:47` |
| `rt_lyon_stroke_tessellate_with_options` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:48` |
| `rt_lyon_stroke_tessellation_free` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:49` |
| `rt_lyon_stroke_tessellation_get_indices` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:51` |
| `rt_lyon_stroke_tessellation_get_vertices` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:50` |
| `rt_lyon_stroke_tessellation_index_count` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:53` |
| `rt_lyon_stroke_tessellation_vertex_count` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:52` |
| `rt_lyon_transform_free` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:74` |
| `rt_lyon_transform_identity` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:69` |
| `rt_lyon_transform_multiply` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:73` |
| `rt_lyon_transform_rotate` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:71` |
| `rt_lyon_transform_scale` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:72` |
| `rt_lyon_transform_translate` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:70` |
| `rt_lyon_vertex_buffer_free` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:56` |
| `rt_lyon_vertex_buffer_get_normal` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:58` |
| `rt_lyon_vertex_buffer_get_position` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:57` |
| `rt_lyon_vertex_buffer_size` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:59` |
| `rt_lyon_vertex_buffer_to_array` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:60` |
| `rt_make_executable` | `extern @ src/compiler/90.tools/sffi_gen/specs/exec_memory.spl:78` |
| `rt_malloc` | `extern @ src/compiler/90.tools/sffi_gen/specs/memory_syscalls.spl:15` |
| `rt_mem_read_i64` | `extern @ src/app/gc/core.spl:420` |
| `rt_mem_read_u8` | `extern @ src/app/gc/core.spl:418` |
| `rt_mem_write_i64` | `extern @ src/app/gc/core.spl:421` |
| `rt_mem_write_u8` | `extern @ src/app/gc/core.spl:419` |
| `rt_memory_barrier__fallback` | `call @ src/lib/nogc_sync_mut/io/volatile_ops.spl:62` |
| `rt_metal_begin_command` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/metal_session.spl:27` |
| `rt_metal_cleanup` | `extern @ src/lib/gc_async_mut/gpu/session/backend_runtime_ops.spl:5` |
| `rt_metal_cleanup_device` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/metal_session.spl:30` |
| `rt_metal_commit_command` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/metal_session.spl:28` |
| `rt_metal_create_library` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/metal_session.spl:25` |
| `rt_metal_create_queue` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/metal_session.spl:24` |
| `rt_metal_device_identity` | `extern @ src/lib/nogc_sync_mut/io/metal_sffi.spl:18` |
| `rt_metal_device_supports_metal3` | `extern @ src/lib/nogc_sync_mut/io/metal_sffi.spl:19` |
| `rt_metal_load_library_bytes` | `extern @ src/lib/nogc_sync_mut/io/metal_sffi.spl:30` |
| `rt_metal_load_library_file` | `extern @ src/lib/nogc_sync_mut/io/metal_sffi.spl:29` |
| `rt_metal_submit` | `extern @ src/lib/gc_async_mut/gpu/session/backend_runtime_ops.spl:3` |
| `rt_metal_wait_completion` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/metal_session.spl:29` |
| `rt_mmap_file` | `extern @ src/compiler/90.tools/sffi_gen/specs/mmap.spl:45` |
| `rt_mmap_read_bytes` | `extern @ src/compiler/90.tools/sffi_gen/specs/mmap.spl:66` |
| `rt_mmap_read_string` | `extern @ src/compiler/90.tools/sffi_gen/specs/mmap.spl:77` |
| `rt_new_function` | `extern @ src/app/audit/ffi_usage.spl:270` |
| `rt_oneapi_device_memory` | `extern @ src/lib/nogc_sync_mut/io/oneapi_sffi.spl:15` |
| `rt_oneapi_device_name` | `extern @ src/lib/nogc_sync_mut/io/oneapi_sffi.spl:13` |
| `rt_oneapi_device_type` | `extern @ src/lib/nogc_sync_mut/io/oneapi_sffi.spl:14` |
| `rt_oneapi_get_device` | `extern @ src/lib/nogc_sync_mut/io/oneapi_sffi.spl:17` |
| `rt_oneapi_get_last_error` | `extern @ src/lib/nogc_sync_mut/io/oneapi_sffi.spl:33` |
| `rt_oneapi_malloc_shared` | `extern @ src/lib/nogc_sync_mut/io/oneapi_sffi.spl:19` |
| `rt_oneapi_memcpy_d2h` | `extern @ src/lib/nogc_sync_mut/io/oneapi_sffi.spl:22` |
| `rt_oneapi_memcpy_h2d` | `extern @ src/lib/nogc_sync_mut/io/oneapi_sffi.spl:21` |
| `rt_oneapi_set_device` | `extern @ src/lib/nogc_sync_mut/io/oneapi_sffi.spl:16` |
| `rt_oneapi_synchronize` | `extern @ src/lib/nogc_sync_mut/io/oneapi_sffi.spl:32` |
| `rt_opengl_get_last_error` | `extern @ src/lib/nogc_sync_mut/io/opengl_sffi.spl:41` |
| `rt_parse_source` | `extern @ src/compiler/90.tools/sffi_gen/specs/compiler_query.spl:123` |
| `rt_password_hash` | `extern @ src/lib/nogc_sync_mut/io/crypto_sffi.spl:25` |
| `rt_password_hash_bcrypt` | `extern @ src/lib/nogc_sync_mut/io/crypto_sffi.spl:30` |
| `rt_password_verify` | `extern @ src/lib/nogc_sync_mut/io/crypto_sffi.spl:26` |
| `rt_password_verify_bcrypt` | `extern @ src/lib/nogc_sync_mut/io/crypto_sffi.spl:31` |
| `rt_path_normalize` | `extern @ src/lib/nogc_sync_mut/sffi/io.spl:266` |
| `rt_print_err` | `extern @ src/app/cli/baremetal_cmd.spl:13` |
| `rt_process_get_rss_kb` | `extern @ src/app/compile/test_dc_leak.spl:5` |
| `rt_process_output` | `extern @ src/lib/nogc_sync_mut/sffi/system.spl:124` |
| `rt_process_run_bounded_tuple` | `call @ src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl:259` |
| `rt_process_run_timeout_tuple` | `call @ src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl:261` |
| `rt_process_run_tuple` | `call @ src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl:258` |
| `rt_ptr_load` | `call @ src/lib/gc_async_mut/simd/scalable.spl:78` |
| `rt_ptr_store` | `call @ src/lib/gc_async_mut/simd/scalable.spl:86` |
| `rt_ptrace_attach` | `extern @ src/lib/nogc_sync_mut/debug/native_agent.spl:10` |
| `rt_ptrace_continue` | `extern @ src/lib/nogc_sync_mut/debug/native_agent.spl:12` |
| `rt_ptrace_detach` | `extern @ src/lib/nogc_sync_mut/debug/native_agent.spl:11` |
| `rt_ptrace_get_registers` | `extern @ src/lib/nogc_sync_mut/debug/native_agent.spl:16` |
| `rt_ptrace_read_memory` | `extern @ src/lib/nogc_sync_mut/debug/native_agent.spl:14` |
| `rt_ptrace_single_step` | `extern @ src/lib/nogc_sync_mut/debug/native_agent.spl:13` |
| `rt_ptrace_wait_stop` | `extern @ src/lib/nogc_sync_mut/debug/native_agent.spl:17` |
| `rt_ptrace_write_memory` | `extern @ src/lib/nogc_sync_mut/debug/native_agent.spl:15` |
| `rt_quic_accept` | `extern @ src/lib/nogc_async_mut/quic/quic_sffi.spl:21` |
| `rt_quic_config_new` | `extern @ src/lib/nogc_async_mut/quic/quic_sffi.spl:13` |
| `rt_quic_config_set_initial_max_streams_bidi` | `extern @ src/lib/nogc_async_mut/quic/quic_sffi.spl:15` |
| `rt_quic_config_set_max_idle_timeout` | `extern @ src/lib/nogc_async_mut/quic/quic_sffi.spl:14` |
| `rt_quic_conn_close` | `extern @ src/lib/nogc_async_mut/quic/quic_sffi.spl:23` |
| `rt_quic_connect` | `extern @ src/lib/nogc_async_mut/quic/quic_sffi.spl:22` |
| `rt_quic_is_closed` | `extern @ src/lib/nogc_async_mut/quic/quic_sffi.spl:51` |
| `rt_quic_is_established` | `extern @ src/lib/nogc_async_mut/quic/quic_sffi.spl:50` |
| `rt_quic_on_timeout` | `extern @ src/lib/nogc_async_mut/quic/quic_sffi.spl:44` |
| `rt_quic_recv` | `extern @ src/lib/nogc_async_mut/quic/quic_sffi.spl:29` |
| `rt_quic_send` | `extern @ src/lib/nogc_async_mut/quic/quic_sffi.spl:30` |
| `rt_quic_stream_recv` | `extern @ src/lib/nogc_async_mut/quic/quic_sffi.spl:36` |
| `rt_quic_stream_send` | `extern @ src/lib/nogc_async_mut/quic/quic_sffi.spl:37` |
| `rt_quic_timeout_as_millis` | `extern @ src/lib/nogc_async_mut/quic/quic_sffi.spl:43` |
| `rt_random_bytes` | `extern @ src/lib/nogc_sync_mut/io/crypto_sffi.spl:49` |
| `rt_range_inclusive_step` | `call @ src/compiler/50.mir/_MirLowering/function_lowering.spl:1146` |
| `rt_range_step` | `call @ src/compiler/50.mir/_MirLowering/function_lowering.spl:1145` |
| `rt_read_u8` | `extern @ src/compiler/90.tools/sffi_gen/specs/memory_syscalls.spl:37` |
| `rt_readline` | `extern @ src/lib/nogc_sync_mut/baremetal/terminal.spl:8` |
| `rt_riscv64_cbo_clean` | `extern @ src/lib/nogc_async_mut_noalloc/baremetal/riscv/cmo.spl:39` |
| `rt_riscv64_cbo_flush` | `extern @ src/lib/nogc_async_mut_noalloc/baremetal/riscv/cmo.spl:41` |
| `rt_riscv64_cbo_inval` | `extern @ src/lib/nogc_async_mut_noalloc/baremetal/riscv/cmo.spl:40` |
| `rt_riscv64_cbo_zero` | `extern @ src/lib/nogc_async_mut_noalloc/baremetal/riscv/cmo.spl:42` |
| `rt_riscv64_fence_i` | `extern @ src/lib/nogc_async_mut_noalloc/baremetal/riscv/cmo.spl:38` |
| `rt_riscv64_prefetch_i` | `extern @ src/lib/nogc_async_mut_noalloc/baremetal/riscv/cmo.spl:45` |
| `rt_riscv64_prefetch_r` | `extern @ src/lib/nogc_async_mut_noalloc/baremetal/riscv/cmo.spl:43` |
| `rt_riscv64_prefetch_w` | `extern @ src/lib/nogc_async_mut_noalloc/baremetal/riscv/cmo.spl:44` |
| `rt_riscv64_sbi_call` | `extern @ src/lib/nogc_async_mut_noalloc/baremetal/riscv/sbi.spl:58` |
| `rt_riscv_has_v_ext` | `extern @ src/compiler/30.types/simd_capabilities.spl:36` |
| `rt_riscv_read_vlenb` | `extern @ src/compiler/30.types/simd_capabilities.spl:33` |
| `rt_riscv_uart_put` | `call @ src/compiler/70.backend/backend/simpleos_native_linkers.spl:370` |
| `rt_rocm3d_available` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/ffi_rocm3d.spl:19` |
| `rt_rocm3d_init` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/ffi_rocm3d.spl:20` |
| `rt_rocm3d_shutdown` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/ffi_rocm3d.spl:21` |
| `rt_rsa_decrypt` | `extern @ src/lib/nogc_sync_mut/io/tls_common_hooks.spl:6` |
| `rt_sdl_event_text` | `extern @ src/lib/editor/70.backend/gui_sdl_bridge.spl:72` |
| `rt_sdn_parse` | `extern @ src/lib/nogc_sync_mut/src/config.spl:9` |
| `rt_serial_available` | `extern @ src/lib/nogc_sync_mut/baremetal/transport/dedicated_hw.spl:11` |
| `rt_serial_set_baud` | `extern @ src/app/io/serial_ffi.spl:24` |
| `rt_serial_set_databits` | `extern @ src/app/io/serial_ffi.spl:26` |
| `rt_serial_set_parity` | `extern @ src/app/io/serial_ffi.spl:25` |
| `rt_serial_set_stopbits` | `extern @ src/app/io/serial_ffi.spl:27` |
| `rt_set_jit_backend` | `call @ src/compiler/95.interp/execution/mod.spl:102` |
| `rt_set_protection` | `extern @ src/compiler/90.tools/sffi_gen/specs/exec_memory.spl:189` |
| `rt_sftp_download` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:53` |
| `rt_sftp_init` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:50` |
| `rt_sftp_mkdir` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:54` |
| `rt_sftp_readdir` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:58` |
| `rt_sftp_rename` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:57` |
| `rt_sftp_rmdir` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:55` |
| `rt_sftp_shutdown` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:51` |
| `rt_sftp_stat` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:59` |
| `rt_sftp_unlink` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:56` |
| `rt_sftp_upload` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:52` |
| `rt_shell` | `extern @ src/lib/nogc_sync_mut/sffi/system.spl:196` |
| `rt_shell_output` | `extern @ src/lib/nogc_sync_mut/sffi/system.spl:201` |
| `rt_simd_mat4_mul_avx2` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/simd_kernels3d.spl:48` |
| `rt_simd_mat4_mul_neon` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/simd_kernels3d.spl:50` |
| `rt_simd_mat4_mul_sse42` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/simd_kernels3d.spl:49` |
| `rt_simd_transform_verts_avx2` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/simd_kernels3d.spl:52` |
| `rt_simd_transform_verts_neon` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/simd_kernels3d.spl:54` |
| `rt_simd_transform_verts_sse42` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/simd_kernels3d.spl:53` |
| `rt_ssh_auth_agent` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:38` |
| `rt_ssh_auth_password` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:36` |
| `rt_ssh_auth_pubkey` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:37` |
| `rt_ssh_channel_close` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:46` |
| `rt_ssh_channel_read` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:44` |
| `rt_ssh_channel_write` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:45` |
| `rt_ssh_connect` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:34` |
| `rt_ssh_disconnect` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:35` |
| `rt_ssh_exec` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:42` |
| `rt_ssh_get_banner` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:69` |
| `rt_ssh_is_authenticated` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:71` |
| `rt_ssh_set_timeout` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:70` |
| `rt_ssh_shell` | `extern @ src/lib/nogc_sync_mut/io/ssh_sffi.spl:43` |
| `rt_stdin_read_bytes` | `extern @ src/app/md_lsp/md_lsp_main.spl:12` |
| `rt_store_barrier__fallback` | `call @ src/lib/nogc_sync_mut/io/volatile_ops.spl:64` |
| `rt_strcat` | `call @ src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1338` |
| `rt_strreplace` | `call @ src/compiler/70.backend/backend/llvm_backend.spl:434` |
| `rt_strsplit` | `call @ src/compiler/70.backend/backend/llvm_backend.spl:435` |
| `rt_substr` | `call @ src/compiler/70.backend/backend/llvm_backend.spl:432` |
| `rt_sysctlbyname_i32` | `extern @ src/compiler/30.types/simd_capabilities.spl:29` |
| `rt_system` | `extern @ src/lib/nogc_sync_mut/baremetal/transport/stlink.spl:8` |
| `rt_tar_add_data` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:39` |
| `rt_tar_add_file` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:38` |
| `rt_tar_close` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:43` |
| `rt_tar_create` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:36` |
| `rt_tar_extract` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:40` |
| `rt_tar_extract_file` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:41` |
| `rt_tar_list` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:42` |
| `rt_tar_open` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:37` |
| `rt_target_arch_name` | `extern @ src/lib/gc_async_mut/gpu/engine2d/render_2d_x86_session.spl:29` |
| `rt_target_pointer_bits` | `extern @ src/lib/gc_async_mut/gpu/engine2d/render_2d_x86_session.spl:30` |
| `rt_targz_create` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:47` |
| `rt_targz_extract` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:48` |
| `rt_tcp_connect` | `extern @ src/app/test_daemon/adapters/hardware_adapter.spl:28` |
| `rt_tcp_connect_timeout` | `extern @ src/lib/nogc_sync_mut/terminal/power/host_power.spl:18` |
| `rt_term_poll` | `extern @ src/app/mem/top_tui.spl:37` |
| `rt_term_read_timeout` | `extern @ src/app/mem/top_tui.spl:36` |
| `rt_test` | `extern @ src/compiler/10.frontend/core/mir/test_mir_lower.spl:79` |
| `rt_test262_eval` | `extern @ src/app/ui.chromium/js_audit.spl:52` |
| `rt_test262_load_corpus` | `extern @ src/app/ui.chromium/js_audit.spl:53` |
| `rt_test_it` | `extern @ src/lib/nogc_sync_mut/spec/decorators.spl:10` |
| `rt_time_day` | `extern @ src/lib/nogc_sync_mut/sffi/system.spl:254` |
| `rt_time_hour` | `extern @ src/lib/nogc_sync_mut/sffi/system.spl:259` |
| `rt_time_millis` | `extern @ src/lib/nogc_sync_mut/sffi/system.spl:237` |
| `rt_time_minute` | `extern @ src/lib/nogc_sync_mut/sffi/system.spl:264` |
| `rt_time_month` | `extern @ src/lib/nogc_sync_mut/sffi/system.spl:249` |
| `rt_time_now_iso` | `extern @ src/lib/nogc_sync_mut/sffi/system.spl:232` |
| `rt_time_now_millis` | `extern @ src/compiler/90.tools/sffi_gen/specs/memory_syscalls.spl:61` |
| `rt_time_now_unix_millis` | `extern @ src/lib/gc_async_mut/gpu/browser_engine/script/js_compat.spl:49` |
| `rt_time_second` | `extern @ src/lib/nogc_sync_mut/sffi/system.spl:269` |
| `rt_time_year` | `extern @ src/lib/nogc_sync_mut/sffi/system.spl:244` |
| `rt_timestamp_diff_seconds` | `extern @ src/lib/nogc_sync_mut/sffi/system.spl:296` |
| `rt_timestamp_from_iso` | `extern @ src/lib/nogc_sync_mut/sffi/system.spl:286` |
| `rt_timestamp_parse` | `extern @ src/lib/nogc_sync_mut/sffi/system.spl:291` |
| `rt_timestamp_to_iso` | `extern @ src/lib/nogc_sync_mut/sffi/system.spl:281` |
| `rt_timestamp_to_string` | `extern @ src/lib/nogc_sync_mut/sffi/system.spl:276` |
| `rt_torch_autograd_detach` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:516` |
| `rt_torch_autograd_requires_grad` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:500` |
| `rt_torch_cuda_empty_cache` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:596` |
| `rt_torch_cuda_max_memory_allocated` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:592` |
| `rt_torch_nn_avg_pool2d` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:448` |
| `rt_torch_nn_batch_norm` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:452` |
| `rt_torch_nn_conv2d` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:440` |
| `rt_torch_nn_dropout` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:460` |
| `rt_torch_nn_embedding` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:468` |
| `rt_torch_nn_layer_norm` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:456` |
| `rt_torch_nn_linear` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:464` |
| `rt_torch_nn_max_pool2d` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:444` |
| `rt_torch_safetensors_close` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:696` |
| `rt_torch_safetensors_get_tensor` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:708` |
| `rt_torch_safetensors_list_names` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:704` |
| `rt_torch_safetensors_num_tensors` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:700` |
| `rt_torch_safetensors_open` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:692` |
| `rt_torch_stream_create` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:560` |
| `rt_torch_tensor_arange` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:81` |
| `rt_torch_tensor_arange_int` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:632` |
| `rt_torch_tensor_empty` | `extern @ src/lib/common/torch/dyn_sffi_ops.spl:857` |
| `rt_torch_tensor_eye` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:89` |
| `rt_torch_tensor_from_i64_data` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:660` |
| `rt_torch_tensor_full` | `extern @ src/lib/common/torch/dyn_sffi_ops.spl:855` |
| `rt_torch_tensor_full_int_1d` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:652` |
| `rt_torch_tensor_full_int_2d` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:656` |
| `rt_torch_tensor_linspace` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:85` |
| `rt_torch_tensor_load` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:684` |
| `rt_torch_tensor_ones` | `extern @ src/lib/common/torch/dyn_sffi_ops.spl:849` |
| `rt_torch_tensor_ones_int_1d` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:644` |
| `rt_torch_tensor_ones_int_2d` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:648` |
| `rt_torch_tensor_rand` | `extern @ src/lib/common/torch/dyn_sffi_ops.spl:851` |
| `rt_torch_tensor_randn` | `extern @ src/lib/common/torch/dyn_sffi_ops.spl:853` |
| `rt_torch_tensor_save` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:680` |
| `rt_torch_tensor_zeros` | `extern @ src/lib/common/torch/dyn_sffi_ops.spl:847` |
| `rt_torch_tensor_zeros_int_1d` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:636` |
| `rt_torch_tensor_zeros_int_2d` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:640` |
| `rt_torch_torchstream_free` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:572` |
| `rt_torch_torchstream_query` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:568` |
| `rt_torch_torchstream_sync` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:564` |
| `rt_torch_torchtensor_abs` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:125` |
| `rt_torch_torchtensor_acos` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:620` |
| `rt_torch_torchtensor_arange` | `extern @ src/lib/common/torch/dyn_sffi_ops.spl:843` |
| `rt_torch_torchtensor_argmax` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:269` |
| `rt_torch_torchtensor_argmin` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:273` |
| `rt_torch_torchtensor_asin` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:616` |
| `rt_torch_torchtensor_atan2` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:624` |
| `rt_torch_torchtensor_cat` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:423` |
| `rt_torch_torchtensor_cat_2` | `extern @ src/lib/common/torch/dyn_sffi_tensor_ops.spl:232` |
| `rt_torch_torchtensor_cat_3` | `extern @ src/lib/common/torch/dyn_sffi_tensor_ops.spl:234` |
| `rt_torch_torchtensor_cat_4` | `extern @ src/lib/common/torch/dyn_sffi_tensor_ops.spl:236` |
| `rt_torch_torchtensor_chunk` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:431` |
| `rt_torch_torchtensor_clone` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:552` |
| `rt_torch_torchtensor_contiguous` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:403` |
| `rt_torch_torchtensor_cos` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:608` |
| `rt_torch_torchtensor_cpu` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:536` |
| `rt_torch_torchtensor_div` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:113` |
| `rt_torch_torchtensor_div_scalar` | `extern @ src/lib/common/torch/dyn_sffi_ops.spl:839` |
| `rt_torch_torchtensor_dot` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:189` |
| `rt_torch_torchtensor_eig` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:221` |
| `rt_torch_torchtensor_exp` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:133` |
| `rt_torch_torchtensor_eye` | `extern @ src/lib/common/torch/dyn_sffi_ops.spl:841` |
| `rt_torch_torchtensor_flatten` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:399` |
| `rt_torch_torchtensor_gather` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:419` |
| `rt_torch_torchtensor_gelu` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:169` |
| `rt_torch_torchtensor_index_select` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:415` |
| `rt_torch_torchtensor_inverse` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:213` |
| `rt_torch_torchtensor_leaky_relu` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:165` |
| `rt_torch_torchtensor_linspace` | `extern @ src/lib/common/torch/dyn_sffi_ops.spl:845` |
| `rt_torch_torchtensor_log` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:137` |
| `rt_torch_torchtensor_log_softmax` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:177` |
| `rt_torch_torchtensor_matmul` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:185` |
| `rt_torch_torchtensor_max_dim` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:255` |
| `rt_torch_torchtensor_mean_dim` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:245` |
| `rt_torch_torchtensor_min_dim` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:265` |
| `rt_torch_torchtensor_neg` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:121` |
| `rt_torch_torchtensor_permute` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:383` |
| `rt_torch_torchtensor_permute_2d` | `extern @ src/lib/common/torch/dyn_sffi_tensor_ops.spl:165` |
| `rt_torch_torchtensor_permute_3d` | `extern @ src/lib/common/torch/dyn_sffi_tensor_ops.spl:167` |
| `rt_torch_torchtensor_permute_4d` | `extern @ src/lib/common/torch/dyn_sffi_tensor_ops.spl:169` |
| `rt_torch_torchtensor_pow` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:117` |
| `rt_torch_torchtensor_relu` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:153` |
| `rt_torch_torchtensor_reshape` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:375` |
| `rt_torch_torchtensor_reshape_1d` | `extern @ src/lib/common/torch/dyn_sffi_tensor_ops.spl:157` |
| `rt_torch_torchtensor_reshape_2d` | `extern @ src/lib/common/torch/dyn_sffi_tensor_ops.spl:159` |
| `rt_torch_torchtensor_reshape_3d` | `extern @ src/lib/common/torch/dyn_sffi_tensor_ops.spl:161` |
| `rt_torch_torchtensor_reshape_4d` | `extern @ src/lib/common/torch/dyn_sffi_tensor_ops.spl:163` |
| `rt_torch_torchtensor_sigmoid` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:157` |
| `rt_torch_torchtensor_sin` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:604` |
| `rt_torch_torchtensor_slice` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:411` |
| `rt_torch_torchtensor_softmax` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:173` |
| `rt_torch_torchtensor_sqrt` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:129` |
| `rt_torch_torchtensor_squeeze` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:387` |
| `rt_torch_torchtensor_squeeze_dim` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:391` |
| `rt_torch_torchtensor_stack` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:427` |
| `rt_torch_torchtensor_stack_2` | `extern @ src/lib/common/torch/dyn_sffi_tensor_ops.spl:238` |
| `rt_torch_torchtensor_stack_3` | `extern @ src/lib/common/torch/dyn_sffi_tensor_ops.spl:240` |
| `rt_torch_torchtensor_stack_4` | `extern @ src/lib/common/torch/dyn_sffi_tensor_ops.spl:242` |
| `rt_torch_torchtensor_sub_scalar` | `extern @ src/lib/common/torch/dyn_sffi_ops.spl:837` |
| `rt_torch_torchtensor_sum_dim` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:235` |
| `rt_torch_torchtensor_svd` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:217` |
| `rt_torch_torchtensor_t` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:197` |
| `rt_torch_torchtensor_tan` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:612` |
| `rt_torch_torchtensor_tanh` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:161` |
| `rt_torch_torchtensor_to_float` | `extern @ src/lib/common/torch/dyn_sffi_tensor_ops.spl:297` |
| `rt_torch_torchtensor_to_float32` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:672` |
| `rt_torch_torchtensor_to_int` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:668` |
| `rt_torch_torchtensor_to_stream` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:548` |
| `rt_torch_torchtensor_transpose` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:193` |
| `rt_torch_torchtensor_unsqueeze` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:395` |
| `rt_torch_torchtensor_view` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:379` |
| `rt_torch_version` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:23` |
| `rt_type_check_ast` | `extern @ src/compiler/90.tools/sffi_gen/specs/compiler_query.spl:190` |
| `rt_type_registry_has` | `extern @ src/compiler/30.types/type_system/builtin_registry.spl:16` |
| `rt_type_registry_lookup` | `extern @ src/compiler/30.types/type_system/builtin_registry.spl:15` |
| `rt_uart_read_byte` | `extern @ src/lib/nogc_async_mut_noalloc/tls/transport.spl:32` |
| `rt_uart_write_byte` | `extern @ src/lib/nogc_async_mut_noalloc/tls/transport.spl:31` |
| `rt_udp_send` | `extern @ src/lib/nogc_sync_mut/terminal/power/host_power.spl:17` |
| `rt_uuid_v4` | `extern @ src/lib/nogc_sync_mut/sffi/system.spl:189` |
| `rt_value_add` | `extern @ src/lib/nogc_sync_mut/ffi/runtime.spl:149` |
| `rt_value_array_new` | `extern @ src/lib/nogc_sync_mut/ffi/runtime.spl:55` |
| `rt_value_as_string` | `extern @ src/lib/nogc_sync_mut/ffi/runtime.spl:128` |
| `rt_value_clone` | `extern @ src/lib/nogc_sync_mut/ffi/runtime.spl:137` |
| `rt_value_dict_new` | `extern @ src/lib/nogc_sync_mut/ffi/runtime.spl:60` |
| `rt_value_div` | `extern @ src/lib/nogc_sync_mut/ffi/runtime.spl:164` |
| `rt_value_free` | `extern @ src/lib/nogc_sync_mut/ffi/runtime.spl:142` |
| `rt_value_is_array` | `extern @ src/lib/nogc_sync_mut/ffi/runtime.spl:99` |
| `rt_value_is_dict` | `extern @ src/lib/nogc_sync_mut/ffi/runtime.spl:104` |
| `rt_value_is_string` | `extern @ src/lib/nogc_sync_mut/ffi/runtime.spl:94` |
| `rt_value_lt` | `extern @ src/lib/nogc_sync_mut/ffi/runtime.spl:176` |
| `rt_value_mul` | `extern @ src/lib/nogc_sync_mut/ffi/runtime.spl:159` |
| `rt_value_string` | `extern @ src/lib/nogc_sync_mut/ffi/runtime.spl:47` |
| `rt_value_sub` | `extern @ src/lib/nogc_sync_mut/ffi/runtime.spl:154` |
| `rt_value_type` | `extern @ src/lib/nogc_sync_mut/ffi/runtime.spl:69` |
| `rt_vk3d_available` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/ffi_vulkan3d.spl:20` |
| `rt_vk3d_init` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/ffi_vulkan3d.spl:21` |
| `rt_vk3d_shutdown` | `extern @ src/lib/nogc_sync_mut/gpu/engine3d/ffi_vulkan3d.spl:22` |
| `rt_vk_alloc_cmd_buffer` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl:37` |
| `rt_vk_begin_cmd` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl:38` |
| `rt_vk_clear` | `extern @ src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_session_runtime_ops.spl:5` |
| `rt_vk_create_allocator` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl:28` |
| `rt_vk_create_cmd_pool` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl:29` |
| `rt_vk_create_descriptor_pool` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl:31` |
| `rt_vk_create_device` | `extern @ src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_session_runtime_ops.spl:2` |
| `rt_vk_create_instance` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl:25` |
| `rt_vk_create_pipeline_cache` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl:30` |
| `rt_vk_destroy_cmd_pool` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl:45` |
| `rt_vk_destroy_device` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl:33` |
| `rt_vk_destroy_instance` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl:34` |
| `rt_vk_device_name` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl:44` |
| `rt_vk_draw_rect` | `extern @ src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_session_runtime_ops.spl:6` |
| `rt_vk_end_cmd` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl:39` |
| `rt_vk_get_queue` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl:27` |
| `rt_vk_has_glslc` | `extern @ src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_session_runtime_ops.spl:4` |
| `rt_vk_has_spirv_support` | `extern @ src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_session_runtime_ops.spl:3` |
| `rt_vk_load_spirv` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl:32` |
| `rt_vk_present` | `extern @ src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_session_runtime_ops.spl:9` |
| `rt_vk_queue_submit` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl:40` |
| `rt_vk_queue_wait_idle` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl:41` |
| `rt_vk_readback` | `extern @ src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_session_runtime_ops.spl:7` |
| `rt_vk_submit` | `extern @ src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_session_runtime_ops.spl:8` |
| `rt_volatile_read_u16__fallback` | `call @ src/lib/nogc_sync_mut/io/volatile_ops.spl:32` |
| `rt_volatile_read_u32__fallback` | `call @ src/lib/nogc_sync_mut/io/volatile_ops.spl:33` |
| `rt_volatile_read_u64__fallback` | `call @ src/lib/nogc_sync_mut/io/volatile_ops.spl:34` |
| `rt_volatile_read_u8__fallback` | `call @ src/lib/nogc_sync_mut/io/volatile_ops.spl:31` |
| `rt_volatile_write_u16__fallback` | `call @ src/lib/nogc_sync_mut/io/volatile_ops.spl:48` |
| `rt_volatile_write_u32__fallback` | `call @ src/lib/nogc_sync_mut/io/volatile_ops.spl:50` |
| `rt_volatile_write_u64__fallback` | `call @ src/lib/nogc_sync_mut/io/volatile_ops.spl:52` |
| `rt_volatile_write_u8__fallback` | `call @ src/lib/nogc_sync_mut/io/volatile_ops.spl:46` |
| `rt_vulkan_api_version` | `extern @ src/lib/nogc_sync_mut/io/vulkan_sffi.spl:39` |
| `rt_watchdog_start` | `extern @ src/lib/nogc_async_mut_noalloc/execution/watchdog_manager.spl:15` |
| `rt_watchdog_stop` | `extern @ src/lib/nogc_async_mut_noalloc/execution/watchdog_manager.spl:16` |
| `rt_webgpu_adapter_is_cpu` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/webgpu_ffi.spl:13` |
| `rt_webgpu_adapter_name` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/webgpu_ffi.spl:12` |
| `rt_webgpu_cleanup` | `extern @ src/lib/gc_async_mut/gpu/session/backend_runtime_ops.spl:16` |
| `rt_webgpu_create_device` | `extern @ src/lib/gc_async_mut/gpu/session/backend_runtime_ops.spl:13` |
| `rt_webgpu_submit` | `extern @ src/lib/gc_async_mut/gpu/session/backend_runtime_ops.spl:14` |
| `rt_wffi_call_void` | `call @ src/compiler/70.backend/wsffi_bindgen.spl:143` |
| `rt_wffi_load` | `call @ src/compiler/70.backend/wsffi_bindgen.spl:121` |
| `rt_wgpu_adapter_backend` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/webgpu_session.spl:25` |
| `rt_wgpu_adapter_name` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/webgpu_session.spl:24` |
| `rt_wgpu_cleanup` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/webgpu_session.spl:32` |
| `rt_wgpu_create_device` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/webgpu_session.spl:27` |
| `rt_wgpu_create_instance` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/webgpu_session.spl:22` |
| `rt_wgpu_create_shader` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/webgpu_session.spl:29` |
| `rt_wgpu_get_queue` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/webgpu_session.spl:28` |
| `rt_wgpu_is_stub` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/webgpu_session.spl:26` |
| `rt_wgpu_present` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/webgpu_session.spl:31` |
| `rt_wgpu_request_adapter` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/webgpu_session.spl:23` |
| `rt_wgpu_submit` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/webgpu_session.spl:30` |
| `rt_wire_to_hex` | `extern @ src/lib/nogc_sync_mut/io/tls_common_hooks.spl:7` |
| `rt_write_exec_memory` | `extern @ src/compiler/90.tools/sffi_gen/specs/exec_memory.spl:60` |
| `rt_write_stdout` | `extern @ src/lib/nogc_sync_mut/io/serial_proxy.spl:13` |
| `rt_ws_close` | `extern @ src/lib/nogc_sync_mut/io/http_sffi.spl:71` |
| `rt_ws_connect` | `extern @ src/lib/nogc_sync_mut/io/http_sffi.spl:68` |
| `rt_ws_receive` | `extern @ src/lib/nogc_sync_mut/io/http_sffi.spl:70` |
| `rt_ws_send` | `extern @ src/lib/nogc_sync_mut/io/http_sffi.spl:69` |
| `rt_zip_add_data` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:28` |
| `rt_zip_add_file` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:27` |
| `rt_zip_close` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:32` |
| `rt_zip_create` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:25` |
| `rt_zip_extract` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:29` |
| `rt_zip_extract_file` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:30` |
| `rt_zip_list` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:31` |
| `rt_zip_open` | `extern @ src/lib/nogc_sync_mut/io/compress_sffi.spl:26` |

### 3a. Full list — referenced, interpreter-dispatch only, no native definition (405)

| symbol | first Simple reference | named in compiler_rust at |
|---|---|---|
| `rt_ast_arg_free` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:153` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:748` |
| `rt_ast_arg_name` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:143` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:546` |
| `rt_ast_arg_value` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:148` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:533` |
| `rt_ast_expr_array_get` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:134` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:702` |
| `rt_ast_expr_array_len` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:129` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:684` |
| `rt_ast_expr_binary_left` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:49` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:369` |
| `rt_ast_expr_binary_op` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:54` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:318` |
| `rt_ast_expr_binary_right` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:59` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:390` |
| `rt_ast_expr_bool_value` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:20` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:280` |
| `rt_ast_expr_call_arg` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:122` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:501` |
| `rt_ast_expr_call_arg_count` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:117` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:483` |
| `rt_ast_expr_call_callee` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:112` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:462` |
| `rt_ast_expr_field_name` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:83` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:666` |
| `rt_ast_expr_field_receiver` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:78` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:646` |
| `rt_ast_expr_float_value` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:30` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:244` |
| `rt_ast_expr_free` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:13` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:730` |
| `rt_ast_expr_ident_name` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:42` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:298` |
| `rt_ast_expr_int_value` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:25` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:226` |
| `rt_ast_expr_method_arg` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:105` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:618` |
| `rt_ast_expr_method_arg_count` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:100` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:600` |
| `rt_ast_expr_method_name` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:95` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:582` |
| `rt_ast_expr_method_receiver` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:90` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:561` |
| `rt_ast_expr_string_value` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:35` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:262` |
| `rt_ast_expr_tag` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:8` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:143` |
| `rt_ast_expr_unary_op` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:66` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:411` |
| `rt_ast_expr_unary_operand` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:71` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:441` |
| `rt_ast_node_free` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:162` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:739` |
| `rt_ast_registry_clear` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:176` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:757` |
| `rt_ast_registry_count` | `extern @ src/lib/nogc_sync_mut/ffi/ast.spl:171` | `src/compiler_rust/compiler/src/interpreter_extern/ast_sffi.rs:782` |
| `rt_async_ws_read_raw` | `extern @ src/lib/nogc_sync_mut/websocket/async_wire_hooks.spl:3` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:639` |
| `rt_async_ws_write_raw` | `extern @ src/lib/nogc_sync_mut/websocket/async_wire_hooks.spl:4` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:640` |
| `rt_audio_backend_name` | `extern @ src/lib/nogc_sync_mut/io/audio_sffi.spl:47` | `src/compiler_rust/compiler/src/interpreter_extern/audio.rs:57` |
| `rt_black_box` | `extern @ src/lib/common/crypto/constant_time.spl:7` | `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:895` |
| `rt_byte_char` | `extern @ src/lib/nogc_sync_mut/io/tls_common_hooks.spl:5` | `src/compiler_rust/compiler/src/interpreter_extern/conversion.rs:136` |
| `rt_bytes_alloc` | `extern @ src/lib/common/memory/packed_span.spl:58` | `src/compiler_rust/compiler/src/interpreter/node_exec.rs:1496` |
| `rt_cargo_fmt` | `extern @ src/lib/nogc_sync_mut/ffi/package.spl:109` | `src/compiler_rust/compiler/src/interpreter_extern/cargo.rs:333` |
| `rt_cargo_lint` | `extern @ src/lib/nogc_sync_mut/ffi/package.spl:114` | `src/compiler_rust/compiler/src/interpreter_extern/cargo.rs:290` |
| `rt_cargo_test` | `extern @ src/lib/nogc_sync_mut/ffi/package.spl:94` | `src/compiler_rust/common/src/runtime_symbols.rs:1526` |
| `rt_cargo_test_doc` | `extern @ src/lib/nogc_sync_mut/ffi/package.spl:99` | `src/compiler_rust/compiler/src/interpreter_extern/cargo.rs:243` |
| `rt_core_as_string` | `call @ src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:123` | `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs:1511` |
| `rt_core_nil` | `call @ src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:986` | `src/compiler_rust/compiler/src/hir/lower/expr/control.rs:2433` |
| `rt_cranelift_aot_define_function` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:479` | `src/compiler_rust/compiler/src/elf_utils.rs:842` |
| `rt_cranelift_append_block_param` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:155` | `src/compiler_rust/compiler/src/elf_utils.rs:920` |
| `rt_cranelift_append_func_params` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:458` | `src/compiler_rust/compiler/src/elf_utils.rs:924` |
| `rt_cranelift_band` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:277` | `src/compiler_rust/compiler/src/elf_utils.rs:868` |
| `rt_cranelift_bconst` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:176` | `src/compiler_rust/compiler/src/elf_utils.rs:855` |
| `rt_cranelift_begin_function` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:76` | `src/compiler_rust/compiler/src/elf_utils.rs:835` |
| `rt_cranelift_bitcast` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:500` | `src/compiler_rust/compiler/src/elf_utils.rs:919` |
| `rt_cranelift_block_param` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:157` | `src/compiler_rust/compiler/src/elf_utils.rs:923` |
| `rt_cranelift_bnot` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:283` | `src/compiler_rust/compiler/src/elf_utils.rs:871` |
| `rt_cranelift_bor` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:279` | `src/compiler_rust/compiler/src/elf_utils.rs:869` |
| `rt_cranelift_brif` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:372` | `src/compiler_rust/compiler/src/elf_utils.rs:882` |
| `rt_cranelift_bxor` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:281` | `src/compiler_rust/compiler/src/elf_utils.rs:870` |
| `rt_cranelift_call` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:413` | `src/compiler_rust/compiler/src/elf_utils.rs:890` |
| `rt_cranelift_call_arg` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:411` | `src/compiler_rust/compiler/src/elf_utils.rs:889` |
| `rt_cranelift_call_args_clear` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:409` | `src/compiler_rust/compiler/src/elf_utils.rs:886` |
| `rt_cranelift_call_function_ptr` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:438` | `src/compiler_rust/compiler/src/elf_utils.rs:930` |
| `rt_cranelift_call_indirect` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:415` | `src/compiler_rust/compiler/src/elf_utils.rs:891` |
| `rt_cranelift_create_block` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:126` | `src/compiler_rust/compiler/src/elf_utils.rs:845` |
| `rt_cranelift_data_addr_in_func` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:51` | `src/compiler_rust/compiler/src/elf_utils.rs:900` |
| `rt_cranelift_declare_function` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:454` | `src/compiler_rust/compiler/src/elf_utils.rs:829` |
| `rt_cranelift_declare_global_data` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:49` | `src/compiler_rust/compiler/src/elf_utils.rs:897` |
| `rt_cranelift_declare_string_data` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:47` | `src/compiler_rust/compiler/src/elf_utils.rs:894` |
| `rt_cranelift_define_function` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:80` | `src/compiler_rust/compiler/src/elf_utils.rs:839` |
| `rt_cranelift_emit_object_raw` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:477` | `src/compiler_rust/compiler/src/elf_utils.rs:934` |
| `rt_cranelift_end_function` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:78` | `src/compiler_rust/compiler/src/elf_utils.rs:838` |
| `rt_cranelift_fadd` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:248` | `src/compiler_rust/compiler/src/elf_utils.rs:864` |
| `rt_cranelift_fcmp` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:326` | `src/compiler_rust/compiler/src/elf_utils.rs:876` |
| `rt_cranelift_fconst` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:174` | `src/compiler_rust/compiler/src/elf_utils.rs:854` |
| `rt_cranelift_fcvt_from_sint` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:506` | `src/compiler_rust/compiler/src/elf_utils.rs:911` |
| `rt_cranelift_fcvt_from_uint` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:508` | `src/compiler_rust/compiler/src/elf_utils.rs:914` |
| `rt_cranelift_fcvt_to_sint` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:502` | `src/compiler_rust/compiler/src/elf_utils.rs:909` |
| `rt_cranelift_fcvt_to_uint` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:504` | `src/compiler_rust/compiler/src/elf_utils.rs:910` |
| `rt_cranelift_fdemote` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:512` | `src/compiler_rust/compiler/src/elf_utils.rs:918` |
| `rt_cranelift_fdiv` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:254` | `src/compiler_rust/compiler/src/elf_utils.rs:867` |
| `rt_cranelift_finalize_module` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:22` | `src/compiler_rust/compiler/src/elf_utils.rs:816` |
| `rt_cranelift_fmul` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:252` | `src/compiler_rust/compiler/src/elf_utils.rs:866` |
| `rt_cranelift_fpromote` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:510` | `src/compiler_rust/compiler/src/elf_utils.rs:917` |
| `rt_cranelift_free_module` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:24` | `src/compiler_rust/compiler/src/elf_utils.rs:819` |
| `rt_cranelift_fsub` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:250` | `src/compiler_rust/compiler/src/elf_utils.rs:865` |
| `rt_cranelift_function_addr_in_func` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:53` | `src/compiler_rust/compiler/src/elf_utils.rs:903` |
| `rt_cranelift_get_function_ptr` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:436` | `src/compiler_rust/compiler/src/elf_utils.rs:927` |
| `rt_cranelift_iadd` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:201` | `src/compiler_rust/compiler/src/elf_utils.rs:857` |
| `rt_cranelift_icmp` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:324` | `src/compiler_rust/compiler/src/elf_utils.rs:875` |
| `rt_cranelift_iconst` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:172` | `src/compiler_rust/compiler/src/elf_utils.rs:853` |
| `rt_cranelift_import_function` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:456` | `src/compiler_rust/compiler/src/elf_utils.rs:832` |
| `rt_cranelift_imul` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:205` | `src/compiler_rust/compiler/src/elf_utils.rs:859` |
| `rt_cranelift_ireduce` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:498` | `src/compiler_rust/compiler/src/elf_utils.rs:908` |
| `rt_cranelift_ishl` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:285` | `src/compiler_rust/compiler/src/elf_utils.rs:872` |
| `rt_cranelift_isub` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:203` | `src/compiler_rust/compiler/src/elf_utils.rs:858` |
| `rt_cranelift_jump` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:370` | `src/compiler_rust/compiler/src/elf_utils.rs:881` |
| `rt_cranelift_load` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:341` | `src/compiler_rust/compiler/src/elf_utils.rs:877` |
| `rt_cranelift_new_aot_module` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:18` | `src/compiler_rust/compiler/src/elf_utils.rs:810` |
| `rt_cranelift_new_aot_module_triple` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:20` | `src/compiler_rust/compiler/src/elf_utils.rs:813` |
| `rt_cranelift_new_module` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:16` | `src/compiler_rust/compiler/src/elf_utils.rs:809` |
| `rt_cranelift_new_module_impl` | `call @ src/compiler/90.tools/sffi_gen/specs/cranelift_advanced.spl:210` | `src/compiler_rust/compiler/src/codegen/cranelift_sffi.rs:307` |
| `rt_cranelift_new_signature` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:103` | `src/compiler_rust/compiler/src/elf_utils.rs:820` |
| `rt_cranelift_null` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:178` | `src/compiler_rust/compiler/src/elf_utils.rs:856` |
| `rt_cranelift_return` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:374` | `src/compiler_rust/compiler/src/elf_utils.rs:883` |
| `rt_cranelift_return_void` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:376` | `src/compiler_rust/compiler/src/elf_utils.rs:884` |
| `rt_cranelift_sdiv` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:207` | `src/compiler_rust/compiler/src/elf_utils.rs:860` |
| `rt_cranelift_seal_all_blocks` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:132` | `src/compiler_rust/compiler/src/elf_utils.rs:850` |
| `rt_cranelift_seal_block` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:130` | `src/compiler_rust/compiler/src/elf_utils.rs:849` |
| `rt_cranelift_sextend` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:494` | `src/compiler_rust/compiler/src/elf_utils.rs:906` |
| `rt_cranelift_sig_add_param` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:105` | `src/compiler_rust/compiler/src/elf_utils.rs:823` |
| `rt_cranelift_sig_set_return` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:107` | `src/compiler_rust/compiler/src/elf_utils.rs:826` |
| `rt_cranelift_srem` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:211` | `src/compiler_rust/compiler/src/elf_utils.rs:862` |
| `rt_cranelift_sshr` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:287` | `src/compiler_rust/compiler/src/elf_utils.rs:873` |
| `rt_cranelift_stack_addr` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:347` | `src/compiler_rust/compiler/src/elf_utils.rs:880` |
| `rt_cranelift_stack_slot` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:345` | `src/compiler_rust/compiler/src/elf_utils.rs:879` |
| `rt_cranelift_store` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:343` | `src/compiler_rust/compiler/src/elf_utils.rs:878` |
| `rt_cranelift_switch_to_block` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:128` | `src/compiler_rust/compiler/src/elf_utils.rs:846` |
| `rt_cranelift_trap` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:378` | `src/compiler_rust/compiler/src/elf_utils.rs:885` |
| `rt_cranelift_udiv` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:209` | `src/compiler_rust/compiler/src/elf_utils.rs:861` |
| `rt_cranelift_uextend` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:496` | `src/compiler_rust/compiler/src/elf_utils.rs:907` |
| `rt_cranelift_urem` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:213` | `src/compiler_rust/compiler/src/elf_utils.rs:863` |
| `rt_cranelift_ushr` | `extern @ src/lib/nogc_sync_mut/sffi/codegen.spl:289` | `src/compiler_rust/compiler/src/elf_utils.rs:874` |
| `rt_cuda_` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/ffi_cuda.spl:7` | `src/compiler_rust/common/src/runtime_symbols.rs:233` |
| `rt_cuda_event_create` | `extern @ src/lib/gc_async_mut/gpu_lane/cuda_native_profile.spl:92` | `src/compiler_rust/common/src/runtime_symbols.rs:1636` |
| `rt_cuda_event_destroy` | `extern @ src/lib/gc_async_mut/gpu_lane/cuda_native_profile.spl:96` | `src/compiler_rust/common/src/runtime_symbols.rs:1640` |
| `rt_cuda_event_elapsed_ns` | `extern @ src/lib/gc_async_mut/gpu_lane/cuda_native_profile.spl:95` | `src/compiler_rust/common/src/runtime_symbols.rs:1639` |
| `rt_cuda_event_record` | `extern @ src/lib/gc_async_mut/gpu_lane/cuda_native_profile.spl:93` | `src/compiler_rust/common/src/runtime_symbols.rs:1637` |
| `rt_cuda_event_synchronize` | `extern @ src/lib/gc_async_mut/gpu_lane/cuda_native_profile.spl:94` | `src/compiler_rust/common/src/runtime_symbols.rs:1638` |
| `rt_cuda_synchronize` | `extern @ src/lib/nogc_async_mut/engine/physics/backend_gpu/gpu_solver.spl:31` | `src/compiler_rust/compiler/src/blocks/math/backend/cuda_eval.rs:33` |
| `rt_env_define_var` | `extern @ src/app/interpreter/ffi/env_ffi.spl:8` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1223` |
| `rt_env_free_handle` | `extern @ src/app/interpreter/ffi/env_ffi.spl:14` | `src/compiler_rust/compiler/src/interpreter_extern/env_sffi.rs:296` |
| `rt_env_get_var` | `extern @ src/app/interpreter/ffi/env_ffi.spl:9` | `src/compiler_rust/compiler/src/interpreter_extern/env_sffi.rs:221` |
| `rt_env_has_var` | `extern @ src/app/interpreter/ffi/env_ffi.spl:11` | `src/compiler_rust/compiler/src/interpreter_extern/env_sffi.rs:256` |
| `rt_env_new_handle` | `extern @ src/app/interpreter/ffi/env_ffi.spl:5` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1234` |
| `rt_env_pop_scope` | `extern @ src/app/interpreter/ffi/env_ffi.spl:7` | `src/compiler_rust/compiler/src/interpreter_extern/env_sffi.rs:187` |
| `rt_env_push_scope` | `extern @ src/app/interpreter/ffi/env_ffi.spl:6` | `src/compiler_rust/compiler/src/interpreter_extern/env_sffi.rs:174` |
| `rt_env_scope_depth` | `extern @ src/app/interpreter/ffi/env_ffi.spl:13` | `src/compiler_rust/compiler/src/interpreter_extern/env_sffi.rs:284` |
| `rt_env_set_var` | `extern @ src/app/interpreter/ffi/env_ffi.spl:10` | `src/compiler_rust/compiler/src/interpreter_extern/env_sffi.rs:237` |
| `rt_env_snapshot` | `extern @ src/app/interpreter/ffi/env_ffi.spl:12` | `src/compiler_rust/compiler/src/interpreter_extern/env_sffi.rs:269` |
| `rt_env_var_count` | `extern @ src/app/interpreter/ffi/env_ffi.spl:15` | `src/compiler_rust/compiler/src/interpreter_extern/env_sffi.rs:305` |
| `rt_env_var_names` | `extern @ src/app/interpreter/ffi/env_ffi.spl:16` | `src/compiler_rust/compiler/src/interpreter_extern/env_sffi.rs:322` |
| `rt_error_arg_count` | `extern @ src/lib/nogc_sync_mut/ffi/error.spl:13` | `src/compiler_rust/compiler/src/interpreter_extern/error_sffi.rs:94` |
| `rt_error_division_by_zero` | `extern @ src/lib/nogc_sync_mut/ffi/error.spl:18` | `src/compiler_rust/compiler/src/interpreter_extern/error_sffi.rs:106` |
| `rt_error_free` | `extern @ src/lib/nogc_sync_mut/ffi/error.spl:55` | `src/compiler_rust/compiler/src/interpreter_extern/error_sffi.rs:161` |
| `rt_error_index_oob` | `extern @ src/lib/nogc_sync_mut/ffi/error.spl:23` | `src/compiler_rust/compiler/src/interpreter_extern/error_sffi.rs:116` |
| `rt_error_message` | `extern @ src/lib/nogc_sync_mut/ffi/error.spl:45` | `src/compiler_rust/compiler/src/interpreter_extern/error_sffi.rs:141` |
| `rt_error_semantic` | `extern @ src/lib/nogc_sync_mut/ffi/error.spl:36` | `src/compiler_rust/compiler/src/interpreter_extern/error_sffi.rs:67` |
| `rt_error_throw` | `extern @ src/lib/nogc_sync_mut/ffi/error.spl:50` | `src/compiler_rust/compiler/src/interpreter_extern/error_sffi.rs:129` |
| `rt_error_type_mismatch` | `extern @ src/lib/nogc_sync_mut/ffi/error.spl:8` | `src/compiler_rust/compiler/src/interpreter_extern/error_sffi.rs:75` |
| `rt_error_undefined_var` | `extern @ src/lib/nogc_sync_mut/ffi/error.spl:31` | `src/compiler_rust/compiler/src/interpreter_extern/error_sffi.rs:83` |
| `rt_event_ports_deregister` | `extern @ src/lib/nogc_async_mut/io/platform_event.spl:149` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1289` |
| `rt_execute_native` | `extern @ src/lib/nogc_sync_mut/sffi/system.spl:114` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1310` |
| `rt_f32_array_alloc` | `extern @ src/lib/common/science_math/perf_sugar.spl:7` | `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:942` |
| `rt_f64_array_alloc` | `extern @ src/lib/common/science_math/perf_sugar.spl:6` | `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:934` |
| `rt_fd_read_until` | `extern @ src/lib/nogc_sync_mut/qemu/qmp_client.spl:15` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1323` |
| `rt_file_atomic_write_mode` | `extern @ src/lib/nogc_sync_mut/terminal/credential/store.spl:35` | `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:706` |
| `rt_file_list_dir` | `extern @ src/lib/nogc_sync_mut/js/node/fs_module.spl:11` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1360` |
| `rt_file_mode` | `extern @ src/lib/nogc_sync_mut/terminal/credential/store.spl:40` | `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:769` |
| `rt_file_modified_time` | `extern @ src/lib/nogc_sync_mut/sffi/io.spl:25` | `src/compiler_rust/driver/src/dependency_cache.rs:6` |
| `rt_fork_parent_stdout` | `extern @ src/lib/nogc_sync_mut/test_runner/test_runner_fork.spl:39` | `src/compiler_rust/compiler/src/pipeline/native_project/tests.rs:2222` |
| `rt_gamepad_count` | `extern @ src/lib/nogc_sync_mut/io/gamepad_sffi.spl:18` | `src/compiler_rust/compiler/src/interpreter_extern/capability_gap.rs:94` |
| `rt_gc_collect` | `extern @ src/lib/nogc_sync_mut/ffi/runtime.spl:13` | `src/compiler_rust/compiler/tests/call_runtime_helpers.rs:73` |
| `rt_get_cwd` | `extern @ src/app/snpm/cmd_init.spl:8` | `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:2120` |
| `rt_glfw_clipboard_get` | `extern @ src/lib/nogc_sync_mut/io/simple_glfw.spl:69` | `src/compiler_rust/compiler/src/interpreter_extern/glfw.rs:24` |
| `rt_glfw_event_text` | `extern @ src/lib/nogc_sync_mut/io/simple_glfw.spl:53` | `src/compiler_rust/compiler/src/interpreter_extern/glfw.rs:24` |
| `rt_gpu_mem_live_bytes` | `extern @ src/lib/nogc_sync_mut/gpu_profile/mem_profile.spl:58` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:68` |
| `rt_gpu_mem_peak_bytes` | `extern @ src/lib/nogc_sync_mut/gpu_profile/mem_profile.spl:59` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:73` |
| `rt_hostname` | `extern @ src/lib/nogc_sync_mut/env/types.spl:13` | `src/compiler_rust/common/src/runtime_symbols.rs:282` |
| `rt_i32_array_alloc` | `extern @ src/lib/common/science_math/perf_sugar.spl:9` | `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:958` |
| `rt_i64_array_alloc` | `extern @ src/lib/common/science_math/perf_sugar.spl:8` | `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:950` |
| `rt_intern_symbol` | `extern @ src/lib/nogc_async_mut/df/mod.spl:3` | `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:966` |
| `rt_iocp_deregister` | `extern @ src/lib/nogc_async_mut/io/platform_event.spl:140` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1277` |
| `rt_jit_backend_name` | `extern @ src/lib/nogc_sync_mut/jit/jit_arm_mixed.spl:19` | `src/compiler_rust/compiler/src/interpreter_extern/jit_native.rs:113` |
| `rt_jit_call_i64` | `extern @ src/lib/nogc_sync_mut/jit/jit_arm_mixed.spl:23` | `src/compiler_rust/compiler/src/interpreter_extern/jit_native.rs:161` |
| `rt_jit_call_i64_i64` | `extern @ src/compiler/95.interp/execution/tiered_jit_manager.spl:20` | `src/compiler_rust/compiler/src/interpreter_extern/jit_native.rs:210` |
| `rt_jit_call_void` | `extern @ src/lib/nogc_sync_mut/jit/tiered_jit.spl:22` | `src/compiler_rust/compiler/src/interpreter_extern/jit_native.rs:186` |
| `rt_jit_cleanup` | `extern @ src/lib/nogc_sync_mut/jit/jit_arm_mixed.spl:27` | `src/compiler_rust/compiler/src/interpreter_extern/jit_native.rs:254` |
| `rt_jit_compile_source` | `extern @ src/lib/nogc_sync_mut/jit/jit_arm_mixed.spl:21` | `src/compiler_rust/compiler/src/interpreter_extern/jit_native.rs:126` |
| `rt_jit_create` | `extern @ src/lib/nogc_sync_mut/jit/jit_arm_mixed.spl:15` | `src/compiler_rust/compiler/src/interpreter_extern/jit_native.rs:63` |
| `rt_jit_create_for_target` | `extern @ src/lib/nogc_sync_mut/jit/jit_arm_mixed.spl:17` | `src/compiler_rust/compiler/src/interpreter_extern/jit_native.rs:76` |
| `rt_jit_has_function` | `extern @ src/lib/nogc_sync_mut/jit/jit_arm_mixed.spl:25` | `src/compiler_rust/compiler/src/interpreter_extern/jit_native.rs:236` |
| `rt_lyon_fill_tessellate` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:38` | `src/compiler_rust/compiler/src/interpreter_extern/capability_gap.rs:14` |
| `rt_lyon_fill_tessellation_free` | `extern @ src/lib/nogc_sync_mut/io/graphics2d_sffi.spl:40` | `src/compiler_rust/compiler/src/interpreter_extern/capability_gap.rs:93` |
| `rt_mem_attr_report` | `extern @ src/lib/nogc_sync_mut/mem/dump.spl:24` | `src/compiler_rust/compiler/src/interpreter_extern/memory.rs:237` |
| `rt_native_build` | `extern @ src/app/cli/bootstrap_main.spl:2` | `src/compiler_rust/compiler/src/native_build_sffi.rs:1` |
| `rt_pool_` | `extern @ src/app/check/concurrency_lint.spl:65` | `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:57` |
| `rt_process_read_stdout` | `extern @ src/lib/nogc_sync_mut/io/process_ops.spl:31` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1662` |
| `rt_process_read_stdout_checked` | `extern @ src/lib/nogc_sync_mut/io/process_ops.spl:33` | `src/compiler_rust/common/src/runtime_symbols.rs:811` |
| `rt_rapier2d_body_apply_force` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:27` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:491` |
| `rt_rapier2d_body_apply_impulse` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:28` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:508` |
| `rt_rapier2d_body_apply_torque` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:29` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:525` |
| `rt_rapier2d_body_free` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:22` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:405` |
| `rt_rapier2d_body_get_mass` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:31` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:543` |
| `rt_rapier2d_body_get_position` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:23` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:415` |
| `rt_rapier2d_body_get_velocity` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:25` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:453` |
| `rt_rapier2d_body_is_sleeping` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:34` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:583` |
| `rt_rapier2d_body_new_dynamic` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:19` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:366` |
| `rt_rapier2d_body_new_kinematic` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:21` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:366` |
| `rt_rapier2d_body_new_static` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:20` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:366` |
| `rt_rapier2d_body_set_angular_damping` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:33` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:569` |
| `rt_rapier2d_body_set_linear_damping` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:32` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:555` |
| `rt_rapier2d_body_set_mass` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:30` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:529` |
| `rt_rapier2d_body_set_position` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:24` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:435` |
| `rt_rapier2d_body_set_velocity` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:26` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:473` |
| `rt_rapier2d_body_wake_up` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:35` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:595` |
| `rt_rapier2d_collider_free` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:42` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:734` |
| `rt_rapier2d_collider_new_box` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:39` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:651` |
| `rt_rapier2d_collider_new_capsule` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:40` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:679` |
| `rt_rapier2d_collider_new_circle` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:38` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:627` |
| `rt_rapier2d_collider_new_polygon` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:41` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:704` |
| `rt_rapier2d_collider_set_density` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:46` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:763` |
| `rt_rapier2d_collider_set_friction` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:45` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:762` |
| `rt_rapier2d_collider_set_offset` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:43` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:743` |
| `rt_rapier2d_collider_set_restitution` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:44` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:761` |
| `rt_rapier2d_collider_set_sensor` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:47` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:767` |
| `rt_rapier2d_contacts_count` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:51` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:790` |
| `rt_rapier2d_contacts_free` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:53` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:826` |
| `rt_rapier2d_contacts_get` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:52` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:800` |
| `rt_rapier2d_get_last_error` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:70` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:887` |
| `rt_rapier2d_joint_distance` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:58` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:852` |
| `rt_rapier2d_joint_fixed` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:61` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:855` |
| `rt_rapier2d_joint_free` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:62` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:859` |
| `rt_rapier2d_joint_prismatic` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:60` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:854` |
| `rt_rapier2d_joint_revolute` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:59` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:853` |
| `rt_rapier2d_joint_set_limits` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:63` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:859` |
| `rt_rapier2d_joint_set_motor` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:64` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:859` |
| `rt_rapier2d_world_body_count` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:67` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:863` |
| `rt_rapier2d_world_cast_ray` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:55` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:848` |
| `rt_rapier2d_world_collider_count` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:68` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:873` |
| `rt_rapier2d_world_free` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:14` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:336` |
| `rt_rapier2d_world_get_contacts` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:50` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:781` |
| `rt_rapier2d_world_intersection_test` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:54` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:832` |
| `rt_rapier2d_world_joint_count` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:69` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:883` |
| `rt_rapier2d_world_new` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:13` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:318` |
| `rt_rapier2d_world_set_gravity` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:16` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:355` |
| `rt_rapier2d_world_step` | `extern @ src/lib/nogc_sync_mut/io/rapier2d_sffi.spl:15` | `src/compiler_rust/compiler/src/interpreter_extern/rapier2d_sffi.rs:342` |
| `rt_readdir_entry` | `extern @ src/lib/nogc_sync_mut/io/dir_entry_ops.spl:10` | `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:2775` |
| `rt_realloc` | `extern @ src/compiler/90.tools/sffi_gen/specs/memory_syscalls.spl:21` | `src/compiler_rust/common/src/runtime_symbols.rs:127` |
| `rt_regex_captures` | `extern @ src/lib/nogc_sync_mut/io/regex_sffi.spl:30` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:332` |
| `rt_regex_captures_len` | `extern @ src/lib/nogc_sync_mut/io/regex_sffi.spl:32` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:333` |
| `rt_regex_destroy` | `extern @ src/lib/nogc_sync_mut/io/regex_sffi.spl:16` | `src/compiler_rust/compiler/src/plugin_manifest.rs:14` |
| `rt_regex_find` | `extern @ src/lib/nogc_sync_mut/io/regex_sffi.spl:23` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:330` |
| `rt_regex_find_all` | `extern @ src/lib/nogc_sync_mut/io/regex_sffi.spl:25` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:331` |
| `rt_regex_find_quick` | `extern @ src/lib/nogc_sync_mut/io/regex_sffi.spl:51` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:338` |
| `rt_regex_is_match` | `extern @ src/lib/nogc_sync_mut/io/regex_sffi.spl:21` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:329` |
| `rt_regex_is_match_quick` | `extern @ src/lib/nogc_sync_mut/io/regex_sffi.spl:49` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:337` |
| `rt_regex_new` | `extern @ src/lib/nogc_sync_mut/io/regex_sffi.spl:14` | `src/compiler_rust/compiler/src/plugin_manifest.rs:14` |
| `rt_regex_replace` | `extern @ src/lib/nogc_sync_mut/io/regex_sffi.spl:37` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:334` |
| `rt_regex_replace_all` | `extern @ src/lib/nogc_sync_mut/io/regex_sffi.spl:39` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:335` |
| `rt_regex_replace_all_quick` | `extern @ src/lib/nogc_sync_mut/io/regex_sffi.spl:55` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:340` |
| `rt_regex_replace_quick` | `extern @ src/lib/nogc_sync_mut/io/regex_sffi.spl:53` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:339` |
| `rt_regex_split` | `extern @ src/lib/nogc_sync_mut/io/regex_sffi.spl:44` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:336` |
| `rt_regex_split_quick` | `extern @ src/lib/nogc_sync_mut/io/regex_sffi.spl:57` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:341` |
| `rt_sdl2_clipboard_get` | `extern @ src/lib/nogc_sync_mut/io/window_sffi.spl:947` | `src/compiler_rust/compiler/src/interpreter_extern/sdl2.rs:62` |
| `rt_sdl2_event_text` | `extern @ src/lib/nogc_sync_mut/io/window_sffi.spl:59` | `src/compiler_rust/compiler/src/interpreter_extern/sdl2.rs:73` |
| `rt_sdl2_get_display_name` | `extern @ src/lib/nogc_sync_mut/desktop/display.spl:6` | `src/compiler_rust/compiler/src/interpreter_extern/sdl2.rs:85` |
| `rt_sdl2_last_error` | `extern @ src/lib/nogc_sync_mut/io/window_sffi.spl:139` | `src/compiler_rust/compiler/src/interpreter_extern/sdl2.rs:103` |
| `rt_sdl3_event_text` | `extern @ src/lib/nogc_sync_mut/io/simple_sdl3.spl:26` | `src/compiler_rust/compiler/src/interpreter_extern/sdl3.rs:24` |
| `rt_sdl3_last_error` | `extern @ src/lib/nogc_sync_mut/io/simple_sdl3.spl:27` | `src/compiler_rust/compiler/src/interpreter_extern/sdl3.rs:24` |
| `rt_shell_exec_tuple` | `extern @ src/lib/nogc_sync_mut/terminal/relay_terminal.spl:23` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1829` |
| `rt_shell_exit_code` | `extern @ src/app/test_daemon/agent_client.spl:17` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1830` |
| `rt_simd_add_f32x8` | `extern @ src/lib/nogc_sync_mut/simd.spl:315` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1832` |
| `rt_simd_add_f64x4` | `extern @ src/lib/nogc_sync_mut/simd.spl:345` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1833` |
| `rt_simd_add_i64x4` | `extern @ src/lib/nogc_sync_mut/simd.spl:569` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1836` |
| `rt_simd_add_u32x4` | `extern @ src/lib/nogc_sync_mut/simd.spl:508` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1837` |
| `rt_simd_and_u32x4` | `extern @ src/lib/nogc_sync_mut/simd.spl:510` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1855` |
| `rt_simd_and_u64x4` | `extern @ src/lib/nogc_sync_mut/simd_crypto.spl:248` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1856` |
| `rt_simd_div_f32x4` | `extern @ src/lib/nogc_sync_mut/simd.spl:288` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1860` |
| `rt_simd_div_f32x8` | `extern @ src/lib/nogc_sync_mut/simd.spl:318` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1861` |
| `rt_simd_div_f64x4` | `extern @ src/lib/nogc_sync_mut/simd.spl:348` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1862` |
| `rt_simd_fma_f32x4` | `extern @ src/lib/nogc_sync_mut/simd.spl:289` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1863` |
| `rt_simd_fma_f32x8` | `extern @ src/lib/nogc_sync_mut/simd.spl:319` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1864` |
| `rt_simd_fma_f64x4` | `extern @ src/lib/nogc_sync_mut/simd.spl:349` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1865` |
| `rt_simd_hadd_f32x4` | `extern @ src/lib/nogc_sync_mut/simd.spl:584` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1866` |
| `rt_simd_hmax_f32x4` | `extern @ src/lib/nogc_sync_mut/simd.spl:585` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1867` |
| `rt_simd_hmin_f32x4` | `extern @ src/lib/nogc_sync_mut/simd.spl:586` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1868` |
| `rt_simd_mul_f32x4` | `extern @ src/lib/nogc_sync_mut/simd.spl:287` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1874` |
| `rt_simd_mul_f32x8` | `extern @ src/lib/nogc_sync_mut/simd.spl:317` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1875` |
| `rt_simd_mul_f64x4` | `extern @ src/lib/nogc_sync_mut/simd.spl:347` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1876` |
| `rt_simd_or_u32x4` | `extern @ src/lib/nogc_sync_mut/simd.spl:511` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1881` |
| `rt_simd_or_u64x4` | `extern @ src/lib/nogc_sync_mut/simd_crypto.spl:249` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1882` |
| `rt_simd_shl_u64x4` | `extern @ src/lib/nogc_sync_mut/simd_crypto.spl:250` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1886` |
| `rt_simd_shr_u64x4` | `extern @ src/lib/nogc_sync_mut/simd_crypto.spl:251` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1890` |
| `rt_simd_shuffle_u8x16` | `extern @ src/lib/nogc_sync_mut/simd_crypto.spl:100` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1887` |
| `rt_simd_sub_f32x4` | `extern @ src/lib/nogc_sync_mut/simd.spl:286` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1896` |
| `rt_simd_sub_f32x8` | `extern @ src/lib/nogc_sync_mut/simd.spl:316` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1897` |
| `rt_simd_sub_f64x4` | `extern @ src/lib/nogc_sync_mut/simd.spl:346` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1898` |
| `rt_simd_sub_i64x4` | `extern @ src/lib/nogc_sync_mut/simd.spl:570` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1901` |
| `rt_simd_sub_u32x4` | `extern @ src/lib/nogc_sync_mut/simd.spl:509` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1902` |
| `rt_simd_vec4u64_get` | `extern @ src/lib/nogc_sync_mut/simd_crypto.spl:245` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1906` |
| `rt_simd_xor_u32x4` | `extern @ src/lib/nogc_sync_mut/simd.spl:512` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1910` |
| `rt_simd_xor_u64x4` | `extern @ src/lib/nogc_sync_mut/simd_crypto.spl:247` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1912` |
| `rt_span_column` | `extern @ src/app/interpreter/ffi/span_ffi.spl:11` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1917` |
| `rt_span_create` | `extern @ src/app/interpreter/ffi/span_ffi.spl:7` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1918` |
| `rt_span_end` | `extern @ src/app/interpreter/ffi/span_ffi.spl:9` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1919` |
| `rt_span_free` | `extern @ src/app/interpreter/ffi/span_ffi.spl:12` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1920` |
| `rt_span_line` | `extern @ src/app/interpreter/ffi/span_ffi.spl:10` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1921` |
| `rt_span_start` | `extern @ src/app/interpreter/ffi/span_ffi.spl:8` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1922` |
| `rt_stdin_read` | `extern @ src/lib/nogc_sync_mut/io/pipe.spl:183` | `src/compiler_rust/compiler/src/linker/native_binary/stubs.rs:267` |
| `rt_stdin_read_all` | `extern @ src/lib/nogc_sync_mut/io/pipe.spl:184` | `src/compiler_rust/compiler/src/linker/native_binary/stubs.rs:268` |
| `rt_stdin_read_line` | `extern @ src/lib/nogc_sync_mut/hooks/stop.spl:158` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:203` |
| `rt_time_monotonic_ns` | `extern @ src/compiler/90.tools/perf/benchmark.spl:205` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2003` |
| `rt_time_now` | `extern @ src/lib/nogc_sync_mut/game2d/time/det_guard.spl:26` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2010` |
| `rt_timestamp_iso8601` | `extern @ src/compiler/90.tools/perf/benchmark.spl:206` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2022` |
| `rt_tls13_hkdf_expand_into` | `extern @ src/lib/nogc_async_mut_noalloc/tls/hkdf.spl:19` | `src/compiler_rust/common/src/runtime_symbols.rs:1004` |
| `rt_tls13_hkdf_expand_label` | `extern @ src/app/test/jit_interp_bridge_array_return_family_probe.spl:29` | `src/compiler_rust/common/src/runtime_symbols.rs:1005` |
| `rt_tls13_hkdf_expand_label_into` | `extern @ src/lib/nogc_async_mut_noalloc/tls/hkdf.spl:20` | `src/compiler_rust/common/src/runtime_symbols.rs:1006` |
| `rt_tls13_hkdf_extract` | `extern @ src/lib/nogc_async_mut_noalloc/tls/hkdf.spl:17` | `src/compiler_rust/common/src/runtime_symbols.rs:1002` |
| `rt_tls13_hkdf_extract_into` | `extern @ src/lib/nogc_async_mut_noalloc/tls/hkdf.spl:18` | `src/compiler_rust/common/src/runtime_symbols.rs:1003` |
| `rt_torch_autograd_backward` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:508` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2037` |
| `rt_torch_autograd_grad` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:504` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2038` |
| `rt_torch_autograd_no_grad_begin` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:520` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2040` |
| `rt_torch_autograd_no_grad_end` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:524` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2043` |
| `rt_torch_autograd_set_requires_grad` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:496` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2045` |
| `rt_torch_autograd_zero_grad` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:512` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2048` |
| `rt_torch_nn_binary_cross_entropy` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:484` | `src/compiler_rust/compiler/src/codegen/instr/core.rs:70` |
| `rt_torch_nn_cross_entropy` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:480` | `src/compiler_rust/compiler/src/codegen/instr/core.rs:69` |
| `rt_torch_nn_mse_loss` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:476` | `src/compiler_rust/compiler/src/codegen/instr/core.rs:68` |
| `rt_torch_nn_nll_loss` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:488` | `src/compiler_rust/compiler/src/codegen/instr/core.rs:71` |
| `rt_torch_torchtensor_add` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:101` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2055` |
| `rt_torch_torchtensor_add_scalar` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:141` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2057` |
| `rt_torch_torchtensor_cuda` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:532` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2060` |
| `rt_torch_torchtensor_det` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:207` | `src/compiler_rust/compiler/src/codegen/instr/core.rs:62` |
| `rt_torch_torchtensor_det_checked` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:209` | `src/compiler_rust/common/src/runtime_symbols.rs:1332` |
| `rt_torch_torchtensor_device` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:544` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2061` |
| `rt_torch_torchtensor_free` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:580` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2062` |
| `rt_torch_torchtensor_is_cuda` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:540` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2063` |
| `rt_torch_torchtensor_max` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:249` | `src/compiler_rust/compiler/src/codegen/instr/core.rs:64` |
| `rt_torch_torchtensor_max_checked` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:251` | `src/compiler_rust/common/src/runtime_symbols.rs:1330` |
| `rt_torch_torchtensor_mean` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:239` | `src/compiler_rust/compiler/src/codegen/instr/core.rs:63` |
| `rt_torch_torchtensor_mean_checked` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:241` | `src/compiler_rust/common/src/runtime_symbols.rs:1328` |
| `rt_torch_torchtensor_min` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:259` | `src/compiler_rust/compiler/src/codegen/instr/core.rs:65` |
| `rt_torch_torchtensor_min_checked` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:261` | `src/compiler_rust/common/src/runtime_symbols.rs:1329` |
| `rt_torch_torchtensor_mul` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:109` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2064` |
| `rt_torch_torchtensor_mul_scalar` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:145` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2066` |
| `rt_torch_torchtensor_ndim` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:363` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2069` |
| `rt_torch_torchtensor_norm` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:201` | `src/compiler_rust/compiler/src/codegen/instr/core.rs:61` |
| `rt_torch_torchtensor_norm_checked` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:203` | `src/compiler_rust/common/src/runtime_symbols.rs:1331` |
| `rt_torch_torchtensor_numel` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:367` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2070` |
| `rt_torch_torchtensor_shape` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:371` | `src/compiler_rust/compiler/src/codegen/instr/core.rs:76` |
| `rt_torch_torchtensor_std` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:277` | `src/compiler_rust/compiler/src/codegen/instr/core.rs:66` |
| `rt_torch_torchtensor_std_checked` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:279` | `src/compiler_rust/common/src/runtime_symbols.rs:1333` |
| `rt_torch_torchtensor_sub` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:105` | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2072` |
| `rt_torch_torchtensor_sum` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:229` | `src/compiler_rust/compiler/src/codegen/instr/core.rs:60` |
| `rt_torch_torchtensor_sum_checked` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:231` | `src/compiler_rust/common/src/runtime_symbols.rs:1327` |
| `rt_torch_torchtensor_var` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:283` | `src/compiler_rust/compiler/src/codegen/instr/core.rs:67` |
| `rt_torch_torchtensor_var_checked` | `extern @ src/lib/nogc_sync_mut/torch/sffi.spl:285` | `src/compiler_rust/common/src/runtime_symbols.rs:1334` |
| `rt_value_print` | `call @ src/compiler/90.tools/sffi_gen/specs/runtime_value_full.spl:531` | `src/compiler_rust/common/src/runtime_symbols.rs:780` |
| `rt_vk_cleanup` | `extern @ src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_session_runtime_ops.spl:10` | `src/compiler_rust/compiler/src/interpreter_extern/capability_gap.rs:91` |
| `rt_vulkan_get_renderdoc_device_pointer` | `extern @ src/app/test/renderdoc_runtime_ops.spl:12` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:3782` |
| `rt_webgpu_adapter_count` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/webgpu_ffi.spl:11` | `src/compiler_rust/compiler/src/interpreter_extern/capability_gap.rs:90` |
| `rt_webgpu_compute_draw` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/webgpu_ffi.spl:10` | `src/compiler_rust/common/src/runtime_symbols.rs:1364` |
| `rt_webgpu_destroy_surface` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/webgpu_ffi.spl:7` | `src/compiler_rust/common/src/runtime_symbols.rs:1361` |
| `rt_webgpu_present` | `extern @ src/lib/gc_async_mut/gpu/session/backend_runtime_ops.spl:15` | `src/compiler_rust/common/src/runtime_symbols.rs:1363` |
| `rt_webgpu_shutdown` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/webgpu_ffi.spl:5` | `src/compiler_rust/common/src/runtime_symbols.rs:1359` |
| `rt_webgpu_upload_pixels` | `extern @ src/lib/nogc_sync_mut/gpu/engine2d/webgpu_ffi.spl:8` | `src/compiler_rust/common/src/runtime_symbols.rs:1362` |
| `rt_wgpu_3d_begin_frame` | `extern @ src/lib/nogc_sync_mut/engine/render/webgpu_backend3d.spl:41` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5088` |
| `rt_wgpu_3d_begin_render_pass` | `extern @ src/lib/nogc_sync_mut/engine/render/webgpu_backend3d.spl:42` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5093` |
| `rt_wgpu_3d_cmd_bind_index_buffer` | `extern @ src/lib/nogc_sync_mut/engine/render/webgpu_backend3d.spl:46` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5113` |
| `rt_wgpu_3d_cmd_bind_texture` | `extern @ src/lib/nogc_sync_mut/engine/render/webgpu_backend3d.spl:47` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5118` |
| `rt_wgpu_3d_cmd_bind_uniform_buffer` | `extern @ src/lib/nogc_sync_mut/engine/render/webgpu_backend3d.spl:48` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5123` |
| `rt_wgpu_3d_cmd_bind_vertex_buffer` | `extern @ src/lib/nogc_sync_mut/engine/render/webgpu_backend3d.spl:45` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5108` |
| `rt_wgpu_3d_cmd_draw_indexed` | `extern @ src/lib/nogc_sync_mut/engine/render/webgpu_backend3d.spl:49` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5128` |
| `rt_wgpu_3d_cmd_set_pipeline` | `extern @ src/lib/nogc_sync_mut/engine/render/webgpu_backend3d.spl:44` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5103` |
| `rt_wgpu_3d_create_buffer` | `extern @ src/lib/nogc_sync_mut/engine/render/webgpu_backend3d.spl:36` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5063` |
| `rt_wgpu_3d_create_pipeline` | `extern @ src/lib/nogc_sync_mut/engine/render/webgpu_backend3d.spl:40` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5083` |
| `rt_wgpu_3d_create_texture` | `extern @ src/lib/nogc_sync_mut/engine/render/webgpu_backend3d.spl:38` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5073` |
| `rt_wgpu_3d_end_frame` | `extern @ src/lib/nogc_sync_mut/engine/render/webgpu_backend3d.spl:50` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5133` |
| `rt_wgpu_3d_end_render_pass` | `extern @ src/lib/nogc_sync_mut/engine/render/webgpu_backend3d.spl:43` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5098` |
| `rt_wgpu_3d_init` | `extern @ src/lib/nogc_sync_mut/engine/render/webgpu_backend3d.spl:35` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5058` |
| `rt_wgpu_3d_present` | `extern @ src/lib/nogc_sync_mut/engine/render/webgpu_backend3d.spl:51` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5138` |
| `rt_wgpu_3d_shutdown` | `extern @ src/lib/nogc_sync_mut/engine/render/webgpu_backend3d.spl:52` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5143` |
| `rt_wgpu_3d_upload_buffer` | `extern @ src/lib/nogc_sync_mut/engine/render/webgpu_backend3d.spl:37` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5068` |
| `rt_wgpu_3d_upload_texture` | `extern @ src/lib/nogc_sync_mut/engine/render/webgpu_backend3d.spl:39` | `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5078` |
| `rt_winit_event_free` | `extern @ src/lib/nogc_sync_mut/game2d/backend/sdl_backend.spl:56` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:381` |
| `rt_winit_event_get_type` | `extern @ src/lib/nogc_sync_mut/game2d/backend/sdl_backend.spl:52` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:457` |
| `rt_winit_event_key_keycode` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:37` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:458` |
| `rt_winit_event_key_packed` | `extern @ src/lib/nogc_sync_mut/game2d/backend/sdl_backend.spl:54` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:460` |
| `rt_winit_event_key_pressed` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:39` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:459` |
| `rt_winit_event_keyboard_input` | `call @ src/lib/nogc_sync_mut/engine/input/input_manager.spl:195` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/winit_sffi_input.rs:108` |
| `rt_winit_event_keyboard_modifiers` | `call @ src/lib/nogc_sync_mut/io/window_sffi.spl:1041` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/winit_sffi_input.rs:133` |
| `rt_winit_event_keyboard_virtual_keycode` | `call @ src/lib/nogc_sync_mut/io/window_sffi.spl:1025` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/winit_sffi_input.rs:125` |
| `rt_winit_event_loop_free` | `extern @ src/lib/nogc_sync_mut/game2d/backend/sdl_backend.spl:44` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:441` |
| `rt_winit_event_loop_new` | `extern @ src/lib/nogc_sync_mut/game2d/backend/sdl_backend.spl:42` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/winit_sffi_window.rs:71` |
| `rt_winit_event_loop_poll_events` | `extern @ src/lib/nogc_sync_mut/game2d/backend/sdl_backend.spl:46` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:445` |
| `rt_winit_event_loop_wait_events` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:33` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:445` |
| `rt_winit_event_mouse_button` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:46` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:462` |
| `rt_winit_event_mouse_moved` | `call @ src/lib/nogc_sync_mut/engine/input/input_manager.spl:220` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/winit_sffi_input.rs:143` |
| `rt_winit_event_mouse_pressed` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:48` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:463` |
| `rt_winit_event_mouse_wheel` | `call @ src/lib/nogc_sync_mut/engine/input/input_manager.spl:228` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/winit_sffi_input.rs:153` |
| `rt_winit_event_mouse_x_milli` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:50` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:472` |
| `rt_winit_event_mouse_y_milli` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:52` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:473` |
| `rt_winit_event_text_byte` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:43` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:468` |
| `rt_winit_event_text_len` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:41` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:461` |
| `rt_winit_event_wheel_y_milli` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:54` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:474` |
| `rt_winit_event_window_close_requested` | `call @ src/lib/nogc_sync_mut/io/window_sffi.spl:1067` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/winit_sffi_events.rs:60` |
| `rt_winit_event_window_x` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:78` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:475` |
| `rt_winit_event_window_y` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:80` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:476` |
| `rt_winit_window_free` | `extern @ src/lib/nogc_sync_mut/game2d/backend/sdl_backend.spl:50` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:440` |
| `rt_winit_window_inner_height` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:68` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:425` |
| `rt_winit_window_inner_width` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:66` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:424` |
| `rt_winit_window_is_fullscreen` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:64` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/winit_sffi_window.rs:507` |
| `rt_winit_window_new` | `extern @ src/lib/nogc_sync_mut/game2d/backend/sdl_backend.spl:48` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/winit_sffi_window.rs:153` |
| `rt_winit_window_position_x` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:72` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:430` |
| `rt_winit_window_position_y` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:74` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:430` |
| `rt_winit_window_present_staged` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:27` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:490` |
| `rt_winit_window_scale_factor_milli` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:70` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:426` |
| `rt_winit_window_set_fullscreen` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:62` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/winit_sffi_window.rs:437` |
| `rt_winit_window_set_position` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:76` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/winit_sffi_window.rs:423` |
| `rt_winit_window_staging_ptr` | `extern @ src/lib/nogc_sync_mut/io/window_winit.spl:25` | `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/mod.rs:59` |

## 4. Known seed facts — verified

### `rt_black_box` — REFUTED as "no definition anywhere", CONFIRMED as no native definition

```
/usr/bin/grep -rn rt_black_box --include=*.c --include=*.h --include=*.rs --include=*.spl src/
```

- No C definition. No `pub extern "C" fn` in `src/compiler_rust/runtime/src/**`.
- It **is** implemented as an interpreter builtin:
  `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:899`
  (`pub fn rt_black_box(args: &[Value]) -> Result<Value, CompileError>`),
  registered at `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:680`.
- Declared at `src/lib/common/crypto/constant_time.spl:7`, called at `:22`.
- **Verdict: sub-bucket 3a.** Fine under the interpreter; an undefined symbol in
  any native link. Note the declaration is `-> i64?` and the call site is
  `rt_black_box(value) ?? value`, so a native miss degrades to the fallback
  rather than crashing — but the constant-time guarantee is then silently lost.

### `rt_host_gpu_active_backend_handle` — CONFIRMED defined nowhere

Exactly two references exist in the entire tree, both in Simple, and no
definition in C, in the Rust runtime crate, or anywhere else in `src/compiler_rust`:

- `src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl:22` — `extern fn rt_host_gpu_active_backend_handle() -> i64`
- `src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl:230` — `val backend_handle = rt_host_gpu_active_backend_handle()`

**Verdict: sub-bucket 3b.** The return type is a bare `i64` with no `?`, so this
is the silent-nil class: an unbacked extern yields nil where an `i64` handle is
expected.

## 5. Windows reachability

Two independent ways a definition can exist in source yet be absent on Windows:
**(a) preprocessor / `cfg` gating** inside a compiled file, and **(b) file-level
gating** — the file is never fed to the compiler on this platform.

### 5a. Preprocessor / cfg gated: no Windows-reachable definition (8)

Classification is **per symbol, not per definition** — the dominant pattern is a
paired `#ifdef _WIN32 ... #else ...`, so a symbol counts as missing on Windows
only when *no* branch of *any* of its definitions is Windows-reachable. On the
Rust side `#[cfg(not(unix))]` / `#[cfg(not(target_os = "macos"))]` are the
**Windows** arms and are correctly treated as reachable.

| symbol | definition | gate | referenced from Simple? |
|---|---|---|---|
| `rt_browser_renderer_namespaces_active` | `C` | `src/runtime/runtime_process.c:2004  cond=['ELSE_OF:IFDEF:_WIN32', 'IFDEF:__linux__']` | no |
| `rt_browser_renderer_preinit_active_for_test` | `C` | `src/runtime/runtime_process.c:2063  cond=['ELSE_OF:IFDEF:_WIN32', 'IFDEF:__linux__']` | no |
| `rt_epoll_create` | `C` | `src/runtime/platform/async_linux_epoll.c:916  cond=['defined(__linux__)']` | no |
| `rt_epoll_ctl` | `C` | `src/runtime/platform/async_linux_epoll.c:921  cond=['defined(__linux__)']` | no |
| `rt_process_owned_test_force_collision` | `C` | `src/runtime/runtime_process_owned.c:134  cond=['!defined(_WIN32) && defined(__unix__)', 'defined(RT_PROCESS_OWNED_TESTING) \|\| defined(RT_PROCESS_OWNED_CORE_ONLY)']` | no |
| `rt_process_owned_test_force_read_failure` | `C` | `src/runtime/runtime_process_owned.c:138  cond=['!defined(_WIN32) && defined(__unix__)', 'defined(RT_PROCESS_OWNED_TESTING) \|\| defined(RT_PROCESS_OWNED_CORE_ONLY)']` | no |
| `rt_process_owned_test_force_signal_failure` | `C` | `src/runtime/runtime_process_owned.c:137  cond=['!defined(_WIN32) && defined(__unix__)', 'defined(RT_PROCESS_OWNED_TESTING) \|\| defined(RT_PROCESS_OWNED_CORE_ONLY)']` | no |
| `rt_process_owned_test_legacy_cancel_v2` | `C` | `src/runtime/runtime_process_owned.c:818  cond=['!defined(_WIN32) && defined(__unix__)', 'defined(RT_PROCESS_OWNED_TESTING) \|\| defined(RT_PROCESS_OWNED_CORE_ONLY)']` | no |

**0 of these 8 are referenced from Simple.** All eight are either C-internal
(`rt_epoll_*` is called from C only), test-only hooks behind
`RT_PROCESS_OWNED_TESTING`, or Linux-only browser-renderer probes. So there is
**no case of a Simple `extern` whose only definition is preprocessor-gated away
on Windows** — the Windows exposure is file-level (5b) and unbacked-extern (§3),
not `#ifdef`.

### 5b. File-level gating (the larger Windows exposure)

A textually unconditional definition still does not exist on Windows if its file
is never compiled. The seed's core-C archive source list is an explicit, closed
list in `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs:338-400`
(`build_c_runtime_library`) — **15 `.c` files**, out of ~117 owned `.c` files
under `src/runtime/`:

```
runtime_native.c runtime_framebuffer.c runtime_directx_core.c runtime_legacy_core.c
runtime_fork.c runtime_memtrack.c runtime_process.c runtime_contracts.c runtime_font.c
runtime_thread.c runtime_simd_utf8.c runtime_simd_case.c runtime_simd_dispatch.c
runtime_packed_span.c runtime_terminal.c
```

plus `hosted_cocoa.c` + `hosted_win32.c` **only when `target.os == Linux`**, and
`runtime_https_openssl_core.c` / `runtime_sqlite.c` behind env/stage flags.

| | count |
|---|---|
| C symbols with a definition in a core-C list file | 745 |
| C symbols defined **only** outside that list | 529 |

Those 529 are not linked into a core-C native build on **any** platform, Windows
included. They are backed only if the Rust runtime also defines them (many are
in the BOTH bucket) or if a different link lane compiles the file.

#### The other lane: the pure-Simple backend has a DIFFERENT list

There are two C source lists, and they do not agree. The self-hosted backend's
list is `src/compiler/70.backend/backend/runtime_compiler.spl:366` — 25
extension-less stems:

```
runtime runtime_native runtime_contracts runtime_rocm runtime_renderdoc
runtime_directx_core runtime_thread runtime_memtrack runtime_timestamp
runtime_fork runtime_process runtime_simd_utf8 runtime_simd_search
runtime_simd_case runtime_simd_dispatch runtime_packed_span runtime_font
runtime_glfw runtime_sdl2 runtime_sdl3 runtime_audio runtime_framebuffer
runtime_image runtime_socket_nonblock counterpart_abi_runtime
```

This matters because per CLAUDE.md the **default tooling is the pure-Simple
self-hosted binary, not the Rust seed** — so this, not the seed list, is the
list that governs a normal `native-build`.

| | count |
|---|---|
| C symbols covered by the seed list (15 files) | 745 |
| C symbols covered by the backend list (25 stems) | 1024 |
| covered by the union of both lists | 1039 |
| C symbols in **neither** list (compiled by no lane) | 235 |
| in the seed list but NOT the backend list | 15 |
| in the backend list but NOT the seed list | 294 |

File-level asymmetries:

- **Seed-only files:** `runtime_legacy_core.c`, `runtime_terminal.c`.
  `runtime_terminal.c` is the notable one — `tools.rs` added it to the seed list
  citing the `rt_unwrap_or_trap` undefined-symbol class, but the pure-Simple
  backend list still does not carry it, so `rt_terminal_*` is exposed to exactly
  that defect on the default lane. (The `tools.rs` comment asserting the
  pure-Simple backend "has always carried runtime_simd_case" is correct for
  `runtime_simd_case` and does not extend to `runtime_terminal`.)
- **Backend-only files (12):** `runtime.c`, `runtime_rocm.c`,
  `runtime_renderdoc.c`, `runtime_timestamp.c`, `runtime_simd_search.c`,
  `runtime_glfw.c`, `runtime_sdl2.c`, `runtime_sdl3.c`, `runtime_audio.c`,
  `runtime_image.c`, `runtime_socket_nonblock.c`, `counterpart_abi_runtime.c`.

Neither list is platform-conditional in its membership except the seed's
Linux-only `hosted_cocoa.c` + `hosted_win32.c` addition, so on Windows the
Cocoa/Win32 hosted providers are compiled by **neither** lane.

Symbols whose only C definition lives in a platform-named file (`hosted_cocoa.c`,
`async_linux_*`, `async_macos.c`, `async_freebsd.c`) — structurally impossible on
Windows (14):

| symbol | file(s) | referenced from Simple? |
|---|---|---|
| `rt_cocoa_event_pump` | `hosted_cocoa.c` | no |
| `rt_cocoa_layer_blend_rect` | `hosted_cocoa.c` | no |
| `rt_cocoa_layer_blur` | `hosted_cocoa.c` | no |
| `rt_cocoa_layer_create` | `hosted_cocoa.c` | no |
| `rt_cocoa_layer_fill_rect` | `hosted_cocoa.c` | no |
| `rt_cocoa_layer_free` | `hosted_cocoa.c` | no |
| `rt_cocoa_layer_gradient_v` | `hosted_cocoa.c` | no |
| `rt_cocoa_layer_present` | `hosted_cocoa.c` | no |
| `rt_cocoa_layer_read_pixel` | `hosted_cocoa.c` | no |
| `rt_cocoa_window_close` | `hosted_cocoa.c` | no |
| `rt_cocoa_window_new` | `hosted_cocoa.c` | no |
| `rt_cocoa_window_resize` | `hosted_cocoa.c` | no |
| `rt_epoll_create` | `async_linux_epoll.c` | no |
| `rt_epoll_ctl` | `async_linux_epoll.c` | no |

## 6. Reproducing these numbers

Coarse counts, directly runnable (GNU grep 3.0 at `/usr/bin/grep`; the wrapped
`grep` on PATH is ugrep honouring `.gitignore` and under-reports):

```sh
cd C:/Users/ormas/dev/simple

# C definitions (the push guard's own regex — single-line signatures only)
/usr/bin/grep -rhoE '^[A-Za-z_][A-Za-z0-9_ \*]*[[:space:]]rt_[A-Za-z0-9_]+[[:space:]]*\([^;]*\)[[:space:]]*\{' \
  --include=*.c --include=*.h src/runtime \
  | /usr/bin/grep -oE 'rt_[A-Za-z0-9_]+' | sort -u | wc -l     # -> 1508

# Rust definitions (push guard regex)
/usr/bin/grep -rhoE 'pub[[:space:]]+(extern[[:space:]]+"C"[[:space:]]+)?fn[[:space:]]+rt_[A-Za-z0-9_]+' \
  --include=*.rs src/compiler_rust/runtime/src \
  | /usr/bin/grep -oE 'rt_[A-Za-z0-9_]+' | sort -u | wc -l     # -> 1804

# Simple extern declarations
/usr/bin/grep -rhoE 'extern[[:space:]]+fn[[:space:]]+rt_[A-Za-z0-9_]+' \
  --include=*.spl src/lib src/compiler src/app \
  | /usr/bin/grep -oE 'rt_[A-Za-z0-9_]+' | sort -u | wc -l     # -> 2283

# The two verified seed facts
/usr/bin/grep -rn rt_black_box --include=*.c --include=*.h --include=*.rs --include=*.spl src/
/usr/bin/grep -rn rt_host_gpu_active_backend_handle --include=*.c --include=*.h --include=*.rs --include=*.spl src/

# The core-C archive source list (file-level gating oracle)
sed -n '338,400p' src/compiler_rust/compiler/src/pipeline/native_project/tools.rs
```

The bucket table in §2 needs comment/literal stripping, balanced-paren matching,
`static` classification and preprocessor-stack tracking, which grep cannot do;
it was produced by a throwaway analysis script run out of the session scratchpad
(deliberately not added to the repo). Its algorithm is fully specified in §1, and
it is a strict superset of the grep regexes above, so the grep numbers bound it
from below (1508 <= 1542 C, 1804 <= 2016 Rust).

## 7. Limits of this census

- **Text analysis, not link analysis.** The authoritative oracle is
  `scripts/check/extern-backing-census.shs`, which reads defined symbol tables
  out of real link artifacts via `nm`. It was deliberately not run: it needs a
  deployed `bin/simple` and a built archive, and a bootstrap was in flight.
- **Definition != correct backing.** A definition present in a compiled file can
  still be a fixed-value stub (`runtime_native_gpu_stub.c`,
  `runtime_hosted_gpu_stubs.c`), and `-fsyntax-only`-clean C says nothing about
  link-time presence.
- **`src/test/**` and `test/**` were not scanned** for references; the census
  covers product source only.
- The `#if` evaluator recognises the macro families actually used in this tree
  (`_WIN32`, `_MSC_VER`, `__linux__`, `__APPLE__`, `__unix__`, `__FreeBSD__`,
  `__NetBSD__`, `__OpenBSD__`, `__EMSCRIPTEN__`, `__ANDROID__`). A gate built
  from a project-specific macro is treated as reachable, so §5a is a *lower*
  bound.
- **Cargo `feature` gates are treated as Windows-reachable.** A Rust definition
  behind `#[cfg(feature = "vulkan")]` counts as defined here; whether the
  feature is enabled in a given build is a separate question this census does
  not answer.
- **Call-site detection is textual.** An `extern fn` declaration is
  unambiguous, but a bare `rt_foo(` match can in principle come from a trailing
  comment on a code line (whole-line `//` and `#` comments are skipped, trailing
  ones are not). 20 randomly sampled NEITHER entries were checked by hand and
  all 20 were genuine (18 `extern fn` declarations, 2 real call sites), but the
  residual risk is non-zero for the call-only entries. Every `extern fn`-backed
  entry is exact.

## Appendix A — the census script, verbatim

Embedded so §2 is reproducible without the session scratchpad. Save as
`census.py` (Python 3.13 used here, no third-party imports), run as
`python3 census.py out.json` from any directory with `ROOT` pointed at the repo.
It prints the four raw extraction counts and writes the full mapping to
`out.json`; the buckets in §2 are set operations on that JSON, spelled out in
§1 and reproduced in Appendix B.

```python
import os, re, sys, json, bisect, collections

ROOT = r"C:\Users\ormas\dev\simple"
EXC_DIRS = {"vendor"}
EXC_FILES = {"miniaudio.h", "stb_image.h", "stb_truetype.h"}


def strip_c(src):
    out = []
    i = 0
    n = len(src)
    while i < n:
        c = src[i]
        if c == '/' and i + 1 < n and src[i + 1] == '/':
            while i < n and src[i] != '\n':
                i += 1
        elif c == '/' and i + 1 < n and src[i + 1] == '*':
            i += 2
            while i + 1 < n and not (src[i] == '*' and src[i + 1] == '/'):
                if src[i] == '\n':
                    out.append('\n')
                i += 1
            i += 2
        elif c == '"' or c == "'":
            q = c
            i += 1
            while i < n and src[i] != q:
                if src[i] == '\\':
                    i += 1
                i += 1
            i += 1
            out.append(' ')
        else:
            out.append(c)
            i += 1
    return ''.join(out)


POSIX_MACROS = r'__linux__|__APPLE__|__FreeBSD__|__unix__|__unix|unix|__NetBSD__|__OpenBSD__|__EMSCRIPTEN__|__ANDROID__|__QNX__|__sun'


def cond_win_reachable(stack):
    for e in stack:
        e = e.strip()
        if e.startswith('ELSE_OF:'):
            inner = e[len('ELSE_OF:'):].strip()
            # else-branch of a windows-positive guard => not windows
            if re.fullmatch(r'IFDEF:\s*(_WIN32|_MSC_VER|WIN32)', inner):
                return False
            if re.fullmatch(r'defined\s*\(?\s*(_WIN32|_MSC_VER|WIN32)\s*\)?', inner):
                return False
            continue
        if e.startswith('ELIF:'):
            e = e[len('ELIF:'):].strip()
        if e.startswith('IFNDEF:'):
            m = e[len('IFNDEF:'):].strip()
            if re.fullmatch(r'(_WIN32|_MSC_VER|WIN32)', m):
                return False
            continue
        if e.startswith('IFDEF:'):
            m = e[len('IFDEF:'):].strip()
            if re.fullmatch(r'(' + POSIX_MACROS + r')', m):
                return False
            continue
        # plain #if expression
        flat = e.replace(' ', '')
        if re.search(r'!defined\(?(_WIN32|_MSC_VER|WIN32)\)?', flat) and not re.search(
                r'(?<!!)defined\(?(_WIN32|_MSC_VER)\)?', flat.replace('!defined(_WIN32)', '').replace('!defined(_MSC_VER)', '')):
            return False
        if re.fullmatch(r'defined\(?(' + POSIX_MACROS + r')\)?', flat):
            return False
        if re.fullmatch(r'(' + POSIX_MACROS + r')', flat):
            return False
    return True


def scan_c():
    defs = collections.defaultdict(list)
    for dp, dns, fns in os.walk(os.path.join(ROOT, 'src', 'runtime')):
        dns[:] = [d for d in dns if d not in EXC_DIRS]
        for fn in fns:
            if not fn.endswith(('.c', '.h')):
                continue
            if fn in EXC_FILES:
                continue
            p = os.path.join(dp, fn)
            rel = os.path.relpath(p, ROOT).replace('\\', '/')
            raw = open(p, encoding='utf-8', errors='replace').read()
            src = strip_c(raw)
            lines = src.split('\n')
            stack = []
            percond = []
            for ln in lines:
                s = ln.strip()
                m = re.match(r'#\s*(ifdef|ifndef|if|elif|else|endif)\b(.*)', s)
                if not m:
                    percond.append(list(stack))
                    continue
                k, rest = m.group(1), m.group(2).strip()
                if k == 'ifdef':
                    stack.append('IFDEF:' + rest)
                elif k == 'ifndef':
                    stack.append('IFNDEF:' + rest)
                elif k == 'if':
                    stack.append(rest)
                elif k == 'elif':
                    if stack:
                        stack[-1] = 'ELIF:' + rest
                elif k == 'else':
                    if stack:
                        stack[-1] = 'ELSE_OF:' + stack[-1]
                elif k == 'endif':
                    if stack:
                        stack.pop()
                percond.append(list(stack))
            offs = []
            o = 0
            for ln in lines:
                offs.append(o)
                o += len(ln) + 1
            for m in re.finditer(r'(?<![A-Za-z0-9_])(rt_[A-Za-z0-9_]+)\s*\(', src):
                name = m.group(1)
                i = m.end() - 1
                depth = 0
                while i < len(src):
                    if src[i] == '(':
                        depth += 1
                    elif src[i] == ')':
                        depth -= 1
                        if depth == 0:
                            break
                    i += 1
                if i >= len(src):
                    continue
                j = i + 1
                while j < len(src) and src[j] in ' \t\n\r':
                    j += 1
                if j >= len(src) or src[j] != '{':
                    continue
                pre = src[max(0, m.start() - 120):m.start()]
                if re.search(r'(\b(if|while|for|switch|return|else)\b|[=&|,;+\-*/!<>?:])\s*$', pre.rstrip()):
                    continue
                lineno = bisect.bisect_right(offs, m.start())
                st = percond[lineno - 1] if lineno - 1 < len(percond) else []
                is_static = bool(re.search(r'\bstatic\b[^;{}()]*$', pre))
                defs[name].append(dict(file=rel, line=lineno, static=is_static,
                                       cond=st, win=cond_win_reachable(st)))
    return defs


def scan_c_macros():
    out = collections.defaultdict(list)
    for dp, dns, fns in os.walk(os.path.join(ROOT, 'src', 'runtime')):
        dns[:] = [d for d in dns if d not in EXC_DIRS]
        for fn in fns:
            if not fn.endswith(('.c', '.h')) or fn in EXC_FILES:
                continue
            p = os.path.join(dp, fn)
            rel = os.path.relpath(p, ROOT).replace('\\', '/')
            for i, ln in enumerate(open(p, encoding='utf-8', errors='replace')):
                m = re.match(r'\s*#\s*define\s+(rt_[A-Za-z0-9_]+)', ln)
                if m:
                    out[m.group(1)].append(f"{rel}:{i+1}")
    return out


def scan_rust():
    defs = collections.defaultdict(list)
    base = os.path.join(ROOT, 'src', 'compiler_rust', 'runtime', 'src')
    for dp, dns, fns in os.walk(base):
        for fn in fns:
            if not fn.endswith('.rs'):
                continue
            p = os.path.join(dp, fn)
            rel = os.path.relpath(p, ROOT).replace('\\', '/')
            lines = open(p, encoding='utf-8', errors='replace').read().split('\n')
            for i, ln in enumerate(lines):
                m = re.search(r'pub\s+(?:unsafe\s+)?(?:extern\s+"C"\s+)?fn\s+(rt_[A-Za-z0-9_]+)', ln)
                if not m:
                    continue
                name = m.group(1)
                cfgs = []
                k = i - 1
                while k >= 0:
                    a = lines[k].strip()
                    if a == '' or a.startswith('///') or a.startswith('//!'):
                        k -= 1
                        continue
                    if a.startswith('#['):
                        cm = re.match(r'#\[cfg\((.*)\)\]$', a)
                        if cm:
                            cfgs.append(cm.group(1))
                        k -= 1
                        continue
                    break
                win = True
                for c in cfgs:
                    if 'windows' in c:
                        continue
                    if re.search(r'\b(unix|target_os\s*=\s*"(linux|macos|freebsd|android|ios)")', c):
                        win = False
                istest = any(re.search(r'\btest\b', c) for c in cfgs) or name.endswith('_test')
                defs[name].append(dict(file=rel, line=i + 1, cfg=cfgs, win=win, test=istest))
    return defs


def scan_spl():
    externs = collections.defaultdict(list)
    calls = collections.defaultdict(list)
    for sub in ('lib', 'compiler', 'app'):
        for dp, dns, fns in os.walk(os.path.join(ROOT, 'src', sub)):
            dns[:] = [d for d in dns if d != 'vendor']
            for fn in fns:
                if not fn.endswith('.spl'):
                    continue
                p = os.path.join(dp, fn)
                rel = os.path.relpath(p, ROOT).replace('\\', '/')
                for i, ln in enumerate(open(p, encoding='utf-8', errors='replace')):
                    st = ln.strip()
                    if st.startswith('//') or st.startswith('#'):
                        continue
                    m = re.search(r'\bextern\s+fn\s+(rt_[A-Za-z0-9_]+)', ln)
                    if m:
                        externs[m.group(1)].append(f"{rel}:{i+1}")
                    for cm in re.finditer(r'(?<![A-Za-z0-9_.])(rt_[A-Za-z0-9_]+)\s*\(', ln):
                        calls[cm.group(1)].append(f"{rel}:{i+1}")
    return externs, calls


cd = scan_c()
cm = scan_c_macros()
rd = scan_rust()
ex, ca = scan_spl()
json.dump({'c': cd, 'cmacro': cm, 'rust': rd, 'ext': ex, 'call': ca},
          open(sys.argv[1], 'w'))
print("c_defs", len(cd), "c_macros", len(cm), "rust_defs", len(rd),
      "externs", len(ex), "callnames", len(ca))

```

## Appendix B — bucket derivation from `out.json`

```python
import json
d = json.load(open('out.json'))
c, r = d['c'], d['rust']
# a static C definition is TU-local and cannot back a Simple extern
cns = {k: v for k, v in ((k, [x for x in v if not x['static']])
                        for k, v in c.items()) if v}
rns = {k: v for k, v in ((k, [x for x in v if not x['test']])
                        for k, v in r.items()) if v}
ref = set(d['ext']) | set(d['call'])
both    = set(cns) & set(rns)      # 560
conly   = set(cns) - set(rns)      # 714
ronly   = set(rns) - set(cns)      # 1454
neither = ref - set(cns) - set(rns)  # 1114   <-- the critical bucket
unref   = (set(cns) | set(rns)) - ref  # 1425
```

