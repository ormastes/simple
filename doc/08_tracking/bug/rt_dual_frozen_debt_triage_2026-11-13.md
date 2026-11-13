# rt_* dual-implementation frozen debt: triage of the 408 unbaselined symbols

Date: 2026-11-13. Base: `46bbec683cc` on `release/1.0.0`.
Gate: `sh scripts/check/check-rt-dual-implementation-ratchet.shs` (frozen mode).

## Counts

| step | verdict |
|------|---------|
| start (`073fe2a89dd`) | 2779 checked, 2490 baselined, 409 new, 120 stale |
| wave 1, PR #8778 (stale rows removed) | 2779 checked, 2370 baselined, 409 new, 0 stale |
| PR #8777 (other lane: C twin for `rt_vulkan_selected_device_identity_v1`) | 2778 checked, 2370 baselined, 408 new, 0 stale |
| wave 2, PR #8787 (this document) | unchanged |
| wave 3, PR #8788 (C twin for `rt_string_to_digit`) | 2777 checked, 2370 baselined, 407 new, 0 stale |
| wave 5 (231 class c and d rows baselined with reasons) | 2777 checked, 2601 baselined, 176 new, 0 stale |

The push tier and the required CI job compare against the base commit, so this
debt fails only the non-required extended job.

## What the gate measures (this decides what can pay the debt)

The guard has exactly two lanes: C (`src/runtime/**/*.c|h`, vendor excluded) and
Rust (`src/compiler_rust/{runtime,native_all,native_loader}/src`). There is no
pure-Simple lane. A pure-Simple implementation of a C-only symbol does not move
the count; only a Rust definition does. That conflicts with "pure Simple first,
C only as a boundary" (`doc/07_guide/os/hal/pure_simple_hal.md`) for 396 of the
408 symbols, which are C-only. Adding Rust twins in bulk to satisfy the count
would grow the seed against that directive, so it was not done.

The C extractor counts every `rt_NAME(...) {` it can see, including `static`
functions and selfcheck sources.

The Rust lane does not include `src/compiler_rust/compiler/src/interpreter_extern`,
where the seed interpreter implements its externs. 86 of the C-only symbols
below are named there (the `interp` column). For the nine thin syscalls and
pure computations listed under class b, each name has a handler definition or
registration there. For those, the seed already has a second implementation;
the guard just cannot see it. The only twin that would move the count is a
further `rt_*` in `runtime/src`, which is neither of the two twin kinds the
directive allows (pure Simple, or C at the boundary), so none was written.

## Classes

| class | meaning | count |
|-------|---------|-------|
| a | dead: no caller, not public API | 0 |
| b | trivial twin | 1 (landed in wave 3) |
| c | host- or platform-specific | 104 |
| d | needs design or owner | 127 |
| S | `static` helper carrying an `rt_` name (not a runtime primitive) | 168 |
| T | defined only in a `src/runtime/test/` selfcheck | 5 |
| X | extractor artifact (the symbol is not really single-lane, or not a definition) | 3 |

### a: none

Candidates were symbols with no `.spl` call site: either no `.spl` mention at
all, or only `extern fn` declarations and comments (none of the non-static
symbols is in the second group). References were collected with
`/usr/bin/grep -rnwF` over `src test examples tools scripts doc config
bootstrap`, limited to source, script, config and doc file types. Each
candidate is either called from other C code, or is
registered public API (`rt_aes_gcm_encrypt_hex`, `rt_aes_gcm_decrypt_hex` in
`config/api/api_registry.sdn`). One symbol has a prototype and a definition and
no caller at all, `rt_gpu_provider_device_identity_raw`
(`src/runtime/runtime_dynload.c`); it sits in the GPU area other lanes are
editing, so it is listed under c and not deleted here.

### b: 1

- `rt_string_to_digit` (rust-only): the seed codegen emits calls to it
  (`codegen/instr/calls.rs`), so a C-runtime link of `.to_digit()` was
  unresolved. C twin landed in wave 3 (PR #8788).

Nine C-only thin syscalls and pure computations first looked like twin
candidates (`rt_page_size`, `rt_mlock`, `rt_munlock`, `rt_madvise_raw`,
`rt_mmap_raw`, `rt_msync_flags`, `rt_db_bitmap_or_u32`,
`rt_db_bitmap_andnot_u32`, `rt_simd_bytes_equal_span`). All nine already have a
seed implementation under `interpreter_extern`, so they moved to class d as a
scope question.

### c: 104

- 57 host-specific (Windows `rt_win*`/`rt_windows_private_*`/`rt_crt_*`, Cocoa,
  Darwin snapshot, SDL2/audio, framebuffer).
- 28 GPU/graphics (engine2d, intel_engine2d, OpenGL, WebGPU backfill, GLFW,
  DirectX, oneAPI). Deferred: active lanes are editing these files.
- 19 optional native library shims (OpenBLAS, CUDA).

None got a stub. A Rust "unavailable" twin for a Windows-only C function would
be new seed code that nothing calls.

### d: 127

- 9: the thin syscalls and pure computations listed under b. Decision needed:
  widen the guard's Rust lane to `interpreter_extern` (as was done for
  `native_all`/`native_loader` on 2026-11-09), or keep them baselined.
- 79: OS process and filesystem security boundary implemented once in C
  (linux group owner, sosix directory roots, hosted safe artifact, owned
  process, secure temp/staging, snapshot nofollow, browser renderer sandbox).
  Same shape as the rows already in the guard's `designed_c_only_allowlist`,
  which needs the repo owner's approval per row.
- 19: non-static C helpers with no `.spl` caller (`rt_observed_malloc_v1`,
  `rt_aes_gcm_*`, `rt_dir_list_cpath`, ...). Either make them `static`/rename,
  or allowlist.
- 16: Simple-facing C primitives with no Rust runtime twin (`rt_http_request`,
  `rt_value_println`, `rt_packed_span_v1_*`, ...).
- 3: Rust-only stateful symbols. `rt_bdd_skipped_count` is a plain Rust
  accessor called by the seed driver (`driver/src/exec_core.rs`); the C runtime
  has no skip counter to read. `rt_browser_http_job_free` and
  `rt_browser_http_job_poll` belong to a Rust-only job registry.
- 1: `rt_unix_socket_connect_timeout`. The Rust lane is a fail-closed stub
  taking `(ptr, len, timeout)`; `runtime.h` declares `(const char*, timeout)`
  with no body; `src/app/build/scheduler/docker_unix_byte_transport.spl` calls
  it. The two lanes need one contract before a twin is honest.

### S and T: 173

These are not runtime primitives. Two ways to clear them:

1. Rename them off the `rt_` prefix. No policy change. It is a removal of
   `rt_*` definitions, so each push needs
   `MUST_CHECK_EXPECT_RUNTIME_API_REMOVALS=<n>`. 43 are in
   `runtime_linux_group_owner_impl.h` and 53 in `runtime_native.c`; the
   Windows-only ones cannot be compiled on this host.
2. Teach the C extractor to skip `static` definitions. Measured effect: the 168
   here go away, and about 308 of the 1072 baselined c-only rows become stale
   and can be deleted. This changes what the gate counts, so it is the owner's
   decision.

### X: 3

- `rt_simd_shl_i32x4`, `rt_simd_shl_i32x8`: reported rust-only, but
  `src/runtime/runtime_simd_dispatch.c` defines both. The extractor rejects a
  definition that directly follows semicolon-less macro invocations such as
  `RT_SIMD_F32X4_BINOP(name, x + y)`, because their `,`/`+` tokens land in the
  declaration prefix. The same blind spot hides four C-only definitions that
  wave 1 had to drop from the baseline as stale (`rt_simd_fma_f32x4`,
  `rt_simd_fma_f32x8`, `rt_simd_fma_f64x4`, `rt_simd_shl_u64x4`). Separately,
  the C `rt_simd_shl_i32x8(int64_t, int64_t)` and the Rust
  `rt_simd_shl_i32x8(*const i32, i64, *mut i32)` do not share an ABI.
- `rt_gui_html_present`: the C side is a `static` function-pointer variable in
  `runtime_native.c`, not a function.

## Next steps, in order

1. Owner decision on S/T: rename (option 1) or extractor skip (option 2).
2. Owner decision on the 79 boundary rows: allowlist or twin.
3. Fix the extractor blind spot after macro invocations; expect 4 c-only rows
   to reappear and 2 rust-only rows to become dual.
4. Owner decision on Rust lane scope: counting `interpreter_extern` handlers
   would make up to 86 of the C-only rows dual without new code.

## Per-symbol table

`spl` is the number of non-test `.spl` lines that mention the symbol. `interp`
is `yes` when the name appears under `interpreter_extern`. The table covers the
408 symbols measured at `46bbec683cc`; `rt_string_to_digit` is marked `done`.

| symbol | lane | class | definition | spl | interp |
|--------|------|-------|------------|-----|--------|
| `rt_aes_gcm_decrypt` | c-only | d | runtime.c | 0 | no |
| `rt_aes_gcm_decrypt_hex` | c-only | d | runtime.c | 0 | no |
| `rt_aes_gcm_decrypt_with_len` | c-only | d | runtime.c | 0 | no |
| `rt_aes_gcm_encrypt` | c-only | d | runtime.c | 0 | no |
| `rt_aes_gcm_encrypt_hex` | c-only | d | runtime.c | 0 | no |
| `rt_aes_gcm_encrypt_with_len` | c-only | d | runtime.c | 0 | no |
| `rt_alloc_observer_success_v1` | c-only | d | runtime_alloc_observer.c | 0 | no |
| `rt_alloc_probe_count_v1` | c-only | d | runtime_alloc_observer.c | 2 | no |
| `rt_alloc_probe_coverage_v1` | c-only | d | runtime_alloc_observer.c | 2 | no |
| `rt_alloc_probe_reset_v1` | c-only | d | runtime_alloc_observer.c | 2 | no |
| `rt_array_write_span_fail_range` | c-only | S | - | 0 | no |
| `rt_audio_play_pcm_f32` | c-only | c | runtime_audio.c | 3 | yes |
| `rt_audio_play_pcm_f64_raw` | c-only | c | runtime_audio.c | 5 | yes |
| `rt_audio_sdl2_queue_pcm_f64_raw` | c-only | c | runtime_sdl2.c | 3 | no |
| `rt_bdd_skipped_count` | rust-only | d | - | 0 | no |
| `rt_blas_daxpy` | c-only | c | scilib/openblas_shim.c | 1 | no |
| `rt_blas_ddot` | c-only | c | scilib/openblas_shim.c | 2 | no |
| `rt_blas_dgemm` | c-only | c | scilib/openblas_shim.c | 3 | no |
| `rt_blas_dgemv` | c-only | c | scilib/openblas_shim.c | 1 | no |
| `rt_browser_http_job_free` | rust-only | d | - | 11 | no |
| `rt_browser_http_job_poll` | rust-only | d | - | 4 | no |
| `rt_browser_renderer_preinit_enter` | c-only | d | runtime_process.c | 1 | no |
| `rt_browser_renderer_spawn_sandboxed` | c-only | d | runtime_process.c | 3 | yes |
| `rt_browser_renderer_write_protocol_some` | c-only | d | runtime_process.c | 3 | yes |
| `rt_browser_renderer_write_stdout_some` | c-only | d | runtime_process.c | 1 | yes |
| `rt_cocoa_layer_blend_rect` | c-only | c | hosted_cocoa.c | 2 | no |
| `rt_cocoa_layer_blur` | c-only | c | hosted_cocoa.c | 2 | no |
| `rt_cocoa_layer_fill_rect` | c-only | c | hosted_cocoa.c | 2 | no |
| `rt_cocoa_layer_gradient_v` | c-only | c | hosted_cocoa.c | 2 | no |
| `rt_cocoa_layer_write_frame` | c-only | c | hosted_cocoa.c | 2 | no |
| `rt_con_complete_prefix` | c-only | S | runtime_console_utf8_private.h | 0 | no |
| `rt_console_write_utf8` | c-only | S | runtime_console_utf8_private.h | 0 | no |
| `rt_core_array_capacity_limit` | c-only | S | runtime_native.c | 0 | no |
| `rt_core_array_capacity_valid` | c-only | S | runtime_native.c | 0 | no |
| `rt_core_array_eq` | c-only | S | runtime_native.c | 0 | no |
| `rt_core_concat_bytes_v1` | c-only | S | runtime_native.c | 0 | no |
| `rt_core_enum_eq` | c-only | S | runtime_native.c | 0 | no |
| `rt_core_file_write_data` | c-only | S | runtime_native.c | 0 | no |
| `rt_core_string_from_data_pointer` | c-only | S | runtime_native.c | 0 | no |
| `rt_core_transient_plan_push` | c-only | S | runtime_native.c | 0 | no |
| `rt_core_transient_text_data_pointer` | c-only | S | runtime_native.c | 1 | no |
| `rt_core_value_eq_inner` | c-only | S | runtime_native.c | 0 | no |
| `rt_counterpart_invoke` | c-only | d | counterpart_abi_runtime.c | 2 | yes |
| `rt_counterpart_open` | c-only | d | counterpart_abi_runtime.c | 2 | yes |
| `rt_crt_fopen` | c-only | S | runtime_crt_file.h | 0 | no |
| `rt_crt_open` | c-only | S | runtime_crt_file.h | 0 | no |
| `rt_crt_wfopen` | c-only | S | runtime_crt_file.h | 0 | no |
| `rt_crt_wopen` | c-only | S | runtime_crt_file.h | 0 | no |
| `rt_db_bitmap_andnot_u32` | c-only | d | runtime_simd_dispatch.c | 2 | yes |
| `rt_db_bitmap_or_u32` | c-only | d | runtime_simd_dispatch.c | 2 | yes |
| `rt_dir_is_real_no_follow` | c-only | d | runtime_secure_staging.c | 6 | yes |
| `rt_dir_list_cpath` | c-only | d | platform/unix_common.h | 0 | no |
| `rt_dir_list_free` | c-only | d | platform/unix_common.h | 0 | no |
| `rt_dir_remove_all_cpath` | c-only | d | platform/unix_common.h | 0 | no |
| `rt_dir_remove_all_impl` | c-only | S | platform/platform_win.h | 0 | no |
| `rt_directx_execute_readback_checked` | c-only | c | runtime_directx_core.c | 2 | yes |
| `rt_directx_rect_valid` | c-only | S | runtime_directx_core.c | 0 | no |
| `rt_directx_stream_valid` | c-only | S | runtime_directx_core.c | 0 | no |
| `rt_disk_headroom_product_v1` | c-only | S | runtime_disk_headroom_private.h | 0 | no |
| `rt_engine2d_blend_const_span_pct_u32` | c-only | c | runtime_simd_dispatch.c | 2 | yes |
| `rt_engine2d_blend_cov_span_u32` | c-only | c | runtime_simd_dispatch.c | 3 | yes |
| `rt_engine2d_blend_mask_span_u32` | c-only | c | runtime_simd_dispatch.c | 2 | yes |
| `rt_engine2d_simd_copy_u32` | c-only | c | runtime_simd_dispatch.c | 0 | no |
| `rt_env_flag_is` | c-only | S | runtime_env_owned.h | 0 | no |
| `rt_env_flag_value` | c-only | S | runtime_env_owned.h | 0 | no |
| `rt_env_owned` | c-only | S | runtime_env_owned.h | 0 | no |
| `rt_env_present` | c-only | S | runtime_env_owned.h | 0 | no |
| `rt_env_snapshot` | c-only | S | runtime_env_owned.h | 4 | yes |
| `rt_fb_blit32` | c-only | c | runtime_framebuffer.c | 4 | yes |
| `rt_fd_stat_ignore_invalid_parameter_v1` | c-only | S | runtime_fd_stat_v1.h | 0 | no |
| `rt_fd_stat_ns_v1` | c-only | S | runtime_fd_stat_v1.h | 0 | no |
| `rt_fd_stat_snapshot_v1_impl` | c-only | S | runtime_fd_stat_v1.h | 0 | no |
| `rt_file_create_excl` | c-only | d | runtime_secure_staging.c | 15 | yes |
| `rt_file_text_at_int` | c-only | S | platform/unix_common.h | 0 | no |
| `rt_file_text_at_string_data` | c-only | S | platform/unix_common.h | 0 | no |
| `rt_fork_parent_wait_bounded` | c-only | d | runtime_fork.c | 2 | no |
| `rt_glfw_present_argb` | c-only | c | runtime_glfw.c | 2 | yes |
| `rt_glfw_present_argb_words_raw` | c-only | c | runtime_glfw.c | 2 | yes |
| `rt_gpu_provider_device_identity_raw` | c-only | c | runtime_dynload.c | 0 | no |
| `rt_group_charge_read_at` | c-only | S | platform/runtime_group_self_charge.h | 0 | no |
| `rt_group_self_charge_snapshot` | c-only | S | platform/runtime_group_self_charge.h | 0 | no |
| `rt_guarded_stop_group` | c-only | S | platform/unix_common.h | 0 | no |
| `rt_gui_html_present` | rust-only | X | - | 0 | no |
| `rt_heap_ref_registered_c` | c-only | d | runtime_native.c | 0 | no |
| `rt_host_commit_headroom_bytes_v1` | c-only | d | runtime_native.c | 5 | yes |
| `rt_host_file_copy_path` | c-only | S | runtime_host_file_exports.c | 0 | no |
| `rt_host_file_copy_tagged_path` | c-only | S | runtime_host_file_exports.c | 0 | no |
| `rt_host_file_owned_bytes` | c-only | S | runtime_host_file_exports.c | 0 | no |
| `rt_host_memory_headroom_bytes_v1` | c-only | d | runtime_memory_headroom.c | 5 | yes |
| `rt_hosted_safe_artifact_bundle3_begin_v1` | c-only | d | runtime_hosted_safe_artifact_bundle_unsupported_v1.c | 2 | no |
| `rt_hosted_safe_artifact_bundle3_finish_v1` | c-only | d | runtime_hosted_safe_artifact_bundle_unsupported_v1.c | 3 | no |
| `rt_hosted_safe_artifact_bundle3_identity_v1` | c-only | d | runtime_hosted_safe_artifact_bundle_unsupported_v1.c | 13 | no |
| `rt_hosted_safe_artifact_bundle3_read_stage_v1` | c-only | d | runtime_hosted_safe_artifact_bundle_unsupported_v1.c | 2 | no |
| `rt_hosted_safe_artifact_bundle3_stage_scr1_v1` | c-only | d | runtime_hosted_safe_artifact_bundle_unsupported_v1.c | 2 | no |
| `rt_hosted_safe_artifact_bundle_n_add_slot_v1` | c-only | d | runtime_hosted_safe_artifact_bundle_unsupported_v1.c | 2 | no |
| `rt_hosted_safe_artifact_bundle_n_begin_two_descriptors_v1` | c-only | d | runtime_hosted_safe_artifact_bundle_unsupported_v1.c | 2 | no |
| `rt_hosted_safe_artifact_bundle_n_begin_v1` | c-only | d | runtime_hosted_safe_artifact_bundle_unsupported_v1.c | 2 | no |
| `rt_hosted_safe_artifact_bundle_n_finish_v1` | c-only | d | runtime_hosted_safe_artifact_bundle_unsupported_v1.c | 8 | no |
| `rt_hosted_safe_artifact_bundle_n_identity_v1` | c-only | d | runtime_hosted_safe_artifact_bundle_unsupported_v1.c | 8 | no |
| `rt_hosted_safe_artifact_bundle_n_read_stage_v1` | c-only | d | runtime_hosted_safe_artifact_bundle_unsupported_v1.c | 2 | no |
| `rt_hosted_safe_artifact_bundle_n_seal_v1` | c-only | d | runtime_hosted_safe_artifact_bundle_unsupported_v1.c | 2 | no |
| `rt_hosted_safe_artifact_bundle_n_stage_descriptor_v1` | c-only | d | runtime_hosted_safe_artifact_bundle_unsupported_v1.c | 2 | no |
| `rt_hosted_safe_artifact_bundle_n_stage_named_descriptor_v1` | c-only | d | runtime_hosted_safe_artifact_bundle_unsupported_v1.c | 2 | no |
| `rt_hosted_safe_artifact_bundle_n_stage_scr1_v1` | c-only | d | runtime_hosted_safe_artifact_bundle_unsupported_v1.c | 2 | no |
| `rt_hosted_safe_artifact_publish_v1` | c-only | d | runtime_hosted_safe_artifact_v1.c | 3 | yes |
| `rt_hosted_safe_artifact_read_v1` | c-only | d | runtime_hosted_safe_artifact_v1.c | 4 | yes |
| `rt_hosted_safe_artifact_root_close_v1` | c-only | d | runtime_hosted_safe_artifact_v1.c | 2 | yes |
| `rt_hosted_safe_artifact_root_open_v1` | c-only | d | runtime_hosted_safe_artifact_v1.c | 3 | yes |
| `rt_hsa_beneath` | c-only | S | runtime_hosted_safe_artifact_v1.c | 0 | no |
| `rt_hsa_bundle` | c-only | S | runtime_hosted_safe_artifact_bundle_v1.c | 0 | no |
| `rt_hsa_bundle_cleanup` | c-only | S | runtime_hosted_safe_artifact_bundle_v1.c | 0 | no |
| `rt_hsa_bundle_close` | c-only | S | runtime_hosted_safe_artifact_bundle_v1.c | 0 | no |
| `rt_hsa_bundle_leaf` | c-only | S | runtime_hosted_safe_artifact_bundle_v1.c | 0 | no |
| `rt_hsa_bundle_name_matches` | c-only | S | runtime_hosted_safe_artifact_bundle_v1.c | 0 | no |
| `rt_hsa_bundle_same_source` | c-only | S | runtime_hosted_safe_artifact_bundle_v1.c | 0 | no |
| `rt_hsa_bundle_unlink` | c-only | S | runtime_hosted_safe_artifact_bundle_v1.c | 0 | no |
| `rt_hsa_close` | c-only | S | runtime_hosted_safe_artifact_v1.c | 0 | no |
| `rt_hsa_fault` | c-only | S | runtime_hosted_safe_artifact_v1.c | 0 | no |
| `rt_hsa_open_root` | c-only | S | runtime_hosted_safe_artifact_v1.c | 0 | no |
| `rt_hsa_openat` | c-only | S | runtime_hosted_safe_artifact_v1.c | 0 | no |
| `rt_hsa_path` | c-only | S | runtime_hosted_safe_artifact_v1.c | 0 | no |
| `rt_hsa_publish` | c-only | S | runtime_hosted_safe_artifact_v1.c | 0 | no |
| `rt_hsa_root` | c-only | S | runtime_hosted_safe_artifact_v1.c | 0 | no |
| `rt_hsa_same_stat` | c-only | S | runtime_hosted_safe_artifact_v1.c | 0 | no |
| `rt_hsa_stat` | c-only | S | runtime_hosted_safe_artifact_v1.c | 0 | no |
| `rt_hsa_sync` | c-only | S | runtime_hosted_safe_artifact_v1.c | 0 | no |
| `rt_hsa_test_fault_v1` | c-only | T | test/rt_hosted_safe_artifact_v1_selfcheck.c | 0 | no |
| `rt_http_append` | c-only | S | runtime_native.c | 0 | no |
| `rt_http_client_request` | c-only | d | runtime_native.c | 2 | no |
| `rt_http_perform` | c-only | S | runtime_native.c | 0 | no |
| `rt_http_request` | c-only | d | runtime_native.c | 62 | yes |
| `rt_http_request_v2` | c-only | d | runtime_native.c | 7 | yes |
| `rt_http_request_with_timeout` | c-only | S | runtime_native.c | 0 | no |
| `rt_http_tuple` | c-only | S | runtime_native.c | 0 | no |
| `rt_http_v2_tuple` | c-only | S | runtime_native.c | 0 | no |
| `rt_http_win_error` | c-only | S | runtime_native.c | 0 | no |
| `rt_http_win_narrow` | c-only | S | runtime_native.c | 0 | no |
| `rt_http_win_timeout` | c-only | S | runtime_native.c | 0 | no |
| `rt_http_win_watchdog_fire` | c-only | S | runtime_native.c | 0 | no |
| `rt_http_win_wide` | c-only | S | runtime_native.c | 0 | no |
| `rt_intel_engine2d_set_args_blit` | c-only | c | runtime_native.c | 4 | no |
| `rt_intel_engine2d_set_args_circle` | c-only | c | runtime_native.c | 4 | no |
| `rt_intel_engine2d_set_args_gradient` | c-only | c | runtime_native.c | 4 | no |
| `rt_intel_engine2d_set_args_line` | c-only | c | runtime_native.c | 4 | no |
| `rt_intel_engine2d_set_args_rect` | c-only | c | runtime_native.c | 4 | no |
| `rt_intel_engine2d_set_args_rounded_rect` | c-only | c | runtime_native.c | 4 | no |
| `rt_intel_engine2d_set_args_triangle` | c-only | c | runtime_native.c | 4 | no |
| `rt_io_tcp_send_no_sigpipe` | c-only | S | runtime_native.c | 0 | no |
| `rt_lapack_dgesv` | c-only | c | scilib/openblas_shim.c | 5 | no |
| `rt_lapack_dgetrf` | c-only | c | scilib/openblas_shim.c | 2 | no |
| `rt_lapack_dgetrs` | c-only | c | scilib/openblas_shim.c | 3 | no |
| `rt_lg_admin_image_v3` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_canonical_path` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_capacity_capability` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_copy_environment` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_copy_text` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_cpu_delegated_v3` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_cpu_readback_v3` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_current_mapping` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_deadline_live_v2` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_delegation_fd` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_digest_fd` | c-only | d | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_free_strings` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_hex_digest` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_is_current_or_parent` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_kill` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_launch_broker_mode_v2` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_memory_delegated` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_now_ms` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_number` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_observation` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_open_absolute_dir` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_parent` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_parent_acquire_at_mode_v3` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_parent_acquire_root` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_parse_membership` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_parse_mountinfo` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_parse_populated` | c-only | S | runtime_linux_cgroup_events_private.h | 0 | no |
| `rt_lg_peak` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_pin_image` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_poll` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_populated` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_profile_parse_v3` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_profile_scope_v3` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_read_at` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_read_fd` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_read_proc_file` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_retain_unlaunched_scope_v2` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_start_mode_v2` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_stream_exec_failed_v2` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_stream_kernel_available_v2` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_stream_request_pinned_v2` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_unix_ms_v2` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_lg_write_at` | c-only | S | runtime_linux_group_owner_impl.h | 0 | no |
| `rt_linux_group_available_capacity_v1` | c-only | d | runtime_linux_group_owner_impl.h | 3 | no |
| `rt_linux_group_cancel_v1` | c-only | d | runtime_linux_group_owner_impl.h | 2 | no |
| `rt_linux_group_collect_v1` | c-only | d | runtime_linux_group_owner_impl.h | 2 | no |
| `rt_linux_group_launch_broker_v1` | c-only | d | runtime_linux_group_owner_impl.h | 3 | no |
| `rt_linux_group_parent_acquire_at_v2` | c-only | d | runtime_linux_group_owner_impl.h | 3 | no |
| `rt_linux_group_parent_acquire_v1` | c-only | d | runtime_linux_group_owner_impl.h | 3 | no |
| `rt_linux_group_parent_release_v1` | c-only | d | runtime_linux_group_owner_impl.h | 2 | no |
| `rt_linux_group_poll_v1` | c-only | d | runtime_linux_group_owner_impl.h | 2 | no |
| `rt_linux_group_start_v1` | c-only | d | runtime_linux_group_owner_impl.h | 3 | no |
| `rt_madvise_raw` | c-only | d | platform/unix_common.h | 2 | yes |
| `rt_mcp_async_std` | c-only | S | runtime_process.c | 0 | no |
| `rt_mem_guard_alloc_sampled` | c-only | S | runtime_memory_guard.h | 0 | no |
| `rt_mem_guard_fault_handler` | c-only | S | runtime_memory_guard.h | 0 | no |
| `rt_mem_guard_fault_report` | c-only | S | runtime_memory_guard.h | 0 | no |
| `rt_mem_guard_find` | c-only | S | runtime_memory_guard.h | 0 | no |
| `rt_mem_guard_free_sampled` | c-only | S | runtime_memory_guard.h | 0 | no |
| `rt_mem_guard_install_handler` | c-only | S | runtime_memory_guard.h | 0 | no |
| `rt_mem_guard_rate` | c-only | S | runtime_memory_guard.h | 0 | no |
| `rt_mem_guard_record_slot` | c-only | S | runtime_memory_guard.h | 0 | no |
| `rt_mem_guard_rep_num` | c-only | S | runtime_memory_guard.h | 0 | no |
| `rt_mem_guard_rep_str` | c-only | S | runtime_memory_guard.h | 0 | no |
| `rt_mem_guard_set_owner` | c-only | S | runtime_memory_guard.h | 0 | no |
| `rt_mem_guard_stats_native` | c-only | S | runtime_memory_guard.h | 0 | no |
| `rt_mlock` | c-only | d | platform/unix_common.h | 4 | yes |
| `rt_mmap_raw` | c-only | d | runtime_native.c | 8 | yes |
| `rt_monotonic_time` | c-only | S | platform/unix_common.h | 0 | no |
| `rt_msync_flags` | c-only | d | platform/unix_common.h | 2 | yes |
| `rt_munlock` | c-only | d | platform/unix_common.h | 4 | yes |
| `rt_native_eq_after` | c-only | T | test/rt_native_eq_heap_vs_raw_empty_literal_selfcheck.c | 0 | no |
| `rt_native_function_word_decode` | c-only | S | runtime_value.h | 0 | no |
| `rt_native_word_exceeds_user_va` | c-only | S | runtime_value.h | 0 | no |
| `rt_observed_calloc_v1` | c-only | d | runtime_alloc_observer.c | 0 | no |
| `rt_observed_malloc_v1` | c-only | d | runtime_alloc_observer.c | 0 | no |
| `rt_observed_realloc_v1` | c-only | d | runtime_alloc_observer.c | 0 | no |
| `rt_oneapi_submit_kernel` | c-only | c | runtime_native.c | 2 | yes |
| `rt_opengl_draw_circle` | c-only | c | runtime_native.c | 2 | yes |
| `rt_opengl_draw_gradient_rect` | c-only | c | runtime_native.c | 2 | yes |
| `rt_opengl_draw_image` | c-only | c | runtime_native.c | 2 | yes |
| `rt_opengl_draw_line` | c-only | c | runtime_native.c | 2 | yes |
| `rt_opengl_draw_rect` | c-only | c | runtime_native.c | 2 | yes |
| `rt_opengl_draw_rounded_rect` | c-only | c | runtime_native.c | 2 | yes |
| `rt_opengl_draw_triangle` | c-only | c | runtime_native.c | 2 | yes |
| `rt_opt_wrap_some` | c-only | S | runtime_native.c | 0 | no |
| `rt_packed_span_v1_probe_verdict` | c-only | d | runtime_packed_span.c | 2 | yes |
| `rt_packed_span_v1_resolve` | c-only | d | runtime_packed_span.c | 0 | no |
| `rt_packed_span_v1_resolve_base` | c-only | d | runtime_packed_span.c | 2 | yes |
| `rt_packed_span_v1_resolve_raw` | c-only | d | runtime_packed_span.c | 0 | yes |
| `rt_page_size` | c-only | d | platform/unix_common.h | 7 | yes |
| `rt_parser_lexical_mask_call_u8x32` | c-only | d | runtime_simd_dispatch.c | 2 | yes |
| `rt_parser_mask_call_u8x32` | c-only | d | runtime_simd_dispatch.c | 2 | yes |
| `rt_process_inspection_v1_input_receipt_value` | c-only | d | runtime_process_owned.c | 3 | no |
| `rt_process_inspection_v1_start_pinned_value` | c-only | d | runtime_process_owned.c | 2 | no |
| `rt_process_observation_v4_reserve_value` | c-only | d | runtime_process_owned.c | 2 | yes |
| `rt_process_observation_v4_reserved_ack_value` | c-only | d | runtime_process_owned.c | 2 | yes |
| `rt_process_observation_v4_reserved_confirm_release_value` | c-only | d | runtime_process_owned.c | 2 | yes |
| `rt_process_observation_v4_reserved_matches_value` | c-only | d | runtime_process_owned.c | 2 | yes |
| `rt_process_observation_v4_reserved_observe_value` | c-only | d | runtime_process_owned.c | 2 | yes |
| `rt_process_observation_v4_reserved_start_pinned_value` | c-only | d | runtime_process_owned.c | 2 | yes |
| `rt_process_observation_v4_reserved_state_value` | c-only | d | runtime_process_owned.c | 2 | yes |
| `rt_process_observation_v4_start_pinned_value` | c-only | d | runtime_process_owned.c | 2 | yes |
| `rt_process_owned_cancel` | c-only | d | runtime_process_owned.c | 0 | no |
| `rt_process_owned_cancel_v2` | c-only | d | runtime_process_owned.c | 0 | no |
| `rt_process_owned_cancel_value` | c-only | d | runtime_process_owned.c | 0 | no |
| `rt_process_owned_collect_v2` | c-only | d | runtime_process_owned.c | 0 | no |
| `rt_process_owned_input_receipt_v3` | c-only | d | runtime_process_owned.c | 0 | no |
| `rt_process_owned_observation_v1` | c-only | d | runtime_process_owned.c | 0 | no |
| `rt_process_owned_poll_v2` | c-only | d | runtime_process_owned.c | 0 | no |
| `rt_process_owned_result_v2` | c-only | d | runtime_process_owned.c | 0 | no |
| `rt_process_owned_start_pinned_v3` | c-only | d | runtime_process_owned.c | 0 | no |
| `rt_process_owned_start_v2` | c-only | d | runtime_process_owned.c | 0 | no |
| `rt_process_owned_start_v3` | c-only | d | runtime_process_owned.c | 0 | no |
| `rt_process_owned_v3_poll_value` | c-only | d | runtime_process_owned.c | 3 | yes |
| `rt_process_owned_v3_set_capture_limits_value` | c-only | d | runtime_process_owned.c | 2 | yes |
| `rt_process_owned_v3_start_pinned_value` | c-only | d | runtime_process_owned.c | 4 | yes |
| `rt_process_owned_v3_start_value` | c-only | d | runtime_process_owned.c | 6 | yes |
| `rt_process_run_owned_bounded` | c-only | d | runtime_process_owned.c | 0 | no |
| `rt_process_run_owned_bounded_value` | c-only | d | runtime_process_owned.c | 2 | no |
| `rt_process_run_owned_observed_bounded` | c-only | d | runtime_process_owned.c | 0 | yes |
| `rt_process_run_owned_observed_bounded_text` | c-only | d | runtime_native.c | 6 | no |
| `rt_process_run_owned_observed_bounded_value` | c-only | d | runtime_process_owned.c | 6 | yes |
| `rt_process_spawn_async_owned_windows` | c-only | c | runtime_process.c | 0 | no |
| `rt_process_spawn_piped_argv` | c-only | S | runtime_process.c | 0 | no |
| `rt_process_write_stdin_some` | c-only | d | runtime_process.c | 3 | yes |
| `rt_rename` | c-only | d | platform/unix_common.h | 0 | no |
| `rt_rsa_decrypt_with_len` | c-only | d | runtime_tls_hosted.c | 0 | no |
| `rt_scilib_cuda_ddot_bits` | c-only | c | scilib/openblas_shim.c | 2 | no |
| `rt_scilib_cuda_dgemm_bits` | c-only | c | scilib/openblas_shim.c | 2 | no |
| `rt_scilib_cuda_dgemv_bits` | c-only | c | scilib/openblas_shim.c | 1 | no |
| `rt_scilib_cuda_dgesv_bits` | c-only | c | scilib/openblas_shim.c | 2 | no |
| `rt_scilib_openblas_daxpy_bits` | c-only | c | scilib/openblas_shim.c | 4 | no |
| `rt_scilib_openblas_ddot_bits` | c-only | c | scilib/openblas_shim.c | 5 | no |
| `rt_scilib_openblas_dgemm_bits` | c-only | c | scilib/openblas_shim.c | 7 | no |
| `rt_scilib_openblas_dgemv_bits` | c-only | c | scilib/openblas_shim.c | 2 | no |
| `rt_scilib_openblas_dgesv_bits` | c-only | c | scilib/openblas_shim.c | 5 | no |
| `rt_scilib_openblas_dgetrf_bits` | c-only | c | scilib/openblas_shim.c | 3 | no |
| `rt_scilib_openblas_dnrm2_bits` | c-only | c | scilib/openblas_shim.c | 3 | no |
| `rt_scilib_openblas_dscal_bits` | c-only | c | scilib/openblas_shim.c | 2 | no |
| `rt_sdr_check_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_close_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_contains_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_create_private_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_find_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_identity_equal_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_location_equal_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_mount_id_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_mount_location_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_mount_unescape_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_open_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_overlap_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_path_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_physical_contains_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_revalidate_pair_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_revalidate_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_root_close_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_root_fast_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_root_open_mode_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_root_open_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_snapshot_v1` | c-only | S | runtime_sosix_directory_roots_v1.h | 0 | no |
| `rt_sdr_values_paths_v1` | c-only | S | runtime_native.c | 0 | no |
| `rt_secure_create_directory_long` | c-only | S | runtime_secure_staging.c | 0 | no |
| `rt_secure_temp_dir` | c-only | d | runtime_secure_staging.c | 14 | yes |
| `rt_secure_temp_dir_core` | c-only | S | runtime_native.c | 0 | no |
| `rt_secure_temp_dir_make` | c-only | d | runtime_secure_temp_split_private.h | 2 | yes |
| `rt_secure_temp_dir_set_parent` | c-only | d | runtime_secure_temp_split_private.h | 5 | yes |
| `rt_secure_temp_dir_set_prefix` | c-only | d | runtime_secure_temp_split_private.h | 3 | yes |
| `rt_simd_bytes_equal_span` | c-only | d | runtime_simd_dispatch.c | 2 | yes |
| `rt_simd_shl_i32x4` | rust-only | X | runtime_simd_dispatch.c | 3 | no |
| `rt_simd_shl_i32x8` | rust-only | X | runtime_simd_dispatch.c | 3 | no |
| `rt_snapshot_readonly_nofollow_v1` | c-only | d | runtime_core_host_services.c | 2 | yes |
| `rt_snapshot_symlink_create_nofollow_v1` | c-only | d | runtime_core_host_services.c | 2 | yes |
| `rt_snapshot_symlink_match_nofollow_v1` | c-only | d | runtime_core_host_services.c | 2 | yes |
| `rt_sosix_darwin_bound_image_v1_start_value` | c-only | c | runtime_sosix_darwin_snapshot_v1_impl.h | 2 | no |
| `rt_sosix_darwin_snapshot_v1_ack_value` | c-only | c | runtime_sosix_darwin_snapshot_v1_impl.h | 2 | yes |
| `rt_sosix_darwin_snapshot_v1_cancel_value` | c-only | c | runtime_sosix_darwin_snapshot_v1_impl.h | 2 | yes |
| `rt_sosix_darwin_snapshot_v1_capabilities_value` | c-only | c | runtime_sosix_darwin_snapshot_v1_impl.h | 2 | yes |
| `rt_sosix_darwin_snapshot_v1_output_value` | c-only | c | runtime_sosix_darwin_snapshot_v1_impl.h | 2 | yes |
| `rt_sosix_darwin_snapshot_v1_poll_value` | c-only | c | runtime_sosix_darwin_snapshot_v1_impl.h | 2 | yes |
| `rt_sosix_darwin_snapshot_v1_start_value` | c-only | c | runtime_sosix_darwin_snapshot_v1_impl.h | 2 | yes |
| `rt_sosix_directory_pair_check_v1` | c-only | d | runtime_native.c | 2 | no |
| `rt_sosix_directory_pair_close_v1` | c-only | d | runtime_native.c | 2 | no |
| `rt_sosix_directory_pair_open_v1` | c-only | d | runtime_native.c | 2 | no |
| `rt_sosix_directory_pair_revalidate_v1` | c-only | d | runtime_native.c | 2 | no |
| `rt_sosix_directory_pair_snapshot_v1` | c-only | d | runtime_native.c | 2 | no |
| `rt_string_index_checked` | c-only | S | runtime_native.c | 0 | no |
| `rt_string_new_uncached_impl` | c-only | S | runtime_native.c | 0 | no |
| `rt_string_to_digit` | rust-only | done | - | 0 | no |
| `rt_sync_instruction_cache` | c-only | S | platform/unix_common.h | 0 | no |
| `rt_text_cmp_any_after` | c-only | T | test/rt_text_cmp_any_heap_vs_raw_selfcheck.c | 0 | no |
| `rt_text_cmp_heap_vs_raw` | c-only | S | - | 0 | no |
| `rt_text_eq_heap_vs_raw` | c-only | T | test/rt_text_cmp_any_heap_vs_raw_selfcheck.c | 0 | no |
| `rt_text_slice_audit_note` | c-only | d | runtime_simd_utf8.c | 0 | no |
| `rt_text_slice_audit_note_range` | c-only | d | - | 3 | no |
| `rt_thread_data_release` | c-only | S | runtime_thread.c | 0 | no |
| `rt_timestamp_oracle_from_components` | c-only | T | test/runtime_timestamp_calendar_oracle.c | 0 | yes |
| `rt_unix_socket_connect_timeout` | rust-only | d | - | 2 | no |
| `rt_value_println` | c-only | d | runtime_native.c | 3 | no |
| `rt_webgpu_create_surface__core_c_backfill` | c-only | c | runtime_native.c | 0 | no |
| `rt_webgpu_destroy_surface__core_c_backfill` | c-only | c | runtime_native.c | 0 | no |
| `rt_webgpu_init__core_c_backfill` | c-only | c | runtime_native.c | 0 | no |
| `rt_webgpu_is_available__core_c_backfill` | c-only | c | runtime_native.c | 0 | no |
| `rt_webgpu_shutdown__core_c_backfill` | c-only | c | runtime_native.c | 0 | no |
| `rt_win32_dib_blend_rect` | c-only | c | hosted_win32.c | 0 | no |
| `rt_win32_dib_blur` | c-only | c | hosted_win32.c | 0 | no |
| `rt_win32_dib_create` | c-only | c | hosted_win32.c | 4 | yes |
| `rt_win32_dib_fill_rect` | c-only | c | hosted_win32.c | 5 | yes |
| `rt_win32_dib_free` | c-only | c | hosted_win32.c | 4 | yes |
| `rt_win32_dib_gradient_v` | c-only | c | hosted_win32.c | 0 | no |
| `rt_win32_dib_present` | c-only | c | hosted_win32.c | 5 | yes |
| `rt_win32_dib_present_rect` | c-only | c | hosted_win32.c | 2 | no |
| `rt_win32_dib_read_pixel` | c-only | c | hosted_win32.c | 4 | yes |
| `rt_win32_dib_resize` | c-only | c | hosted_win32.c | 2 | no |
| `rt_win32_message_pump` | c-only | c | hosted_win32.c | 3 | yes |
| `rt_win32_window_close` | c-only | c | hosted_win32.c | 6 | yes |
| `rt_win32_window_new` | c-only | c | hosted_win32.c | 5 | yes |
| `rt_win32_window_resize` | c-only | c | hosted_win32.c | 2 | no |
| `rt_win_create_directory_utf8` | c-only | S | platform/platform_win.h | 0 | no |
| `rt_win_env_fits` | c-only | S | runtime_native.c | 0 | no |
| `rt_win_excl_open_regular_no_follow` | c-only | S | platform/runtime_win_excl_file.h | 0 | no |
| `rt_win_file_copy_create_excl_no_follow` | c-only | S | platform/runtime_win_excl_file.h | 0 | no |
| `rt_win_file_link_create_excl_no_follow` | c-only | S | platform/runtime_win_excl_file.h | 0 | no |
| `rt_win_fopen_read_shared` | c-only | S | platform/runtime_win_long_path.h | 0 | no |
| `rt_win_long_path_rename` | c-only | S | platform/runtime_win_long_path.h | 0 | no |
| `rt_win_long_path_widen` | c-only | S | platform/runtime_win_long_path.h | 0 | yes |
| `rt_win_private_atomic_write` | c-only | S | platform/runtime_windows_private_atomic.h | 0 | no |
| `rt_win_profile_path_parents_are_real` | c-only | S | platform/runtime_win_long_path.h | 0 | yes |
| `rt_win_remove_tree_utf8` | c-only | S | platform/runtime_win_remove_tree.h | 0 | no |
| `rt_win_remove_tree_wide` | c-only | S | platform/runtime_win_remove_tree.h | 0 | no |
| `rt_win_rename_posix_replace` | c-only | S | platform/runtime_win_long_path.h | 0 | no |
| `rt_windows_build_command_line` | c-only | c | platform/platform_win.h | 0 | no |
| `rt_windows_private_adopt_published_read_v2` | c-only | c | platform/runtime_windows_private_root.h | 3 | no |
| `rt_windows_private_alloc_v1` | c-only | c | platform/runtime_windows_private_root.h | 9 | no |
| `rt_windows_private_check_v1` | c-only | c | platform/runtime_windows_private_root.h | 3 | no |
| `rt_windows_private_directory_v1` | c-only | c | platform/runtime_windows_private_root.h | 3 | no |
| `rt_windows_private_file_close_v1` | c-only | c | platform/runtime_windows_private_root.h | 3 | no |
| `rt_windows_private_file_read_v1` | c-only | c | platform/runtime_windows_private_root.h | 3 | no |
| `rt_windows_private_file_seal_v1` | c-only | c | platform/runtime_windows_private_root.h | 3 | no |
| `rt_windows_private_file_size_v1` | c-only | c | platform/runtime_windows_private_root.h | 4 | no |
| `rt_windows_private_file_v1` | c-only | c | platform/runtime_windows_private_root.h | 3 | no |
| `rt_windows_private_file_write_v1` | c-only | c | platform/runtime_windows_private_root.h | 4 | no |
| `rt_windows_private_free_v1` | c-only | c | platform/runtime_windows_private_root.h | 22 | no |
| `rt_windows_private_publish_v1` | c-only | c | platform/runtime_windows_private_root.h | 3 | no |
| `rt_windows_private_read_directory_v2` | c-only | c | platform/runtime_windows_private_root.h | 3 | no |
| `rt_windows_private_read_file_check_v2` | c-only | c | platform/runtime_windows_private_root.h | 3 | no |
| `rt_windows_private_read_file_close_v2` | c-only | c | platform/runtime_windows_private_root.h | 3 | no |
| `rt_windows_private_read_file_open_v2` | c-only | c | platform/runtime_windows_private_root.h | 3 | no |
| `rt_windows_private_read_file_read_v2` | c-only | c | platform/runtime_windows_private_root.h | 3 | no |
| `rt_windows_private_read_file_size_v2` | c-only | c | platform/runtime_windows_private_root.h | 4 | no |
| `rt_windows_private_read_root_close_v2` | c-only | c | platform/runtime_windows_private_root.h | 3 | no |
| `rt_windows_private_read_root_open_v2` | c-only | c | platform/runtime_windows_private_root.h | 3 | no |
| `rt_windows_private_read_root_ready_v2` | c-only | c | platform/runtime_windows_private_root.h | 3 | no |
| `rt_windows_private_root_close_v1` | c-only | c | platform/runtime_windows_private_root.h | 3 | no |
| `rt_windows_private_root_open_v1` | c-only | c | platform/runtime_windows_private_root.h | 3 | no |
| `rt_windows_private_root_ready_v1` | c-only | c | platform/runtime_windows_private_root.h | 4 | no |
| `rt_windows_private_roots_same_directory_v2` | c-only | c | platform/runtime_windows_private_root.h | 3 | no |
