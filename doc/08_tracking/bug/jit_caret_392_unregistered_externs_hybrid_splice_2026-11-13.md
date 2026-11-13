# Caret JIT run splices 392 externs through the interpreter (unregistered JIT symbols)

- **Filed:** 2026-11-13
- **Status:** OPEN. Out of scope for lane `work/jit-dynamic-dispatch-20261113`; tracked here only.
- **Related:** `doc/05_design/compiler/jit/jit_trait_dispatch_and_cross_module_link.md` (row 5)

## Symptom

`SIMPLE_RUST_SEED_WARNING=0 <seed> run src/app/llm_caret/main.spl --help`
(seed `a64ac53aaf6ca014`, `origin/release/1.0.0` `fe75b13a584`) prints:

```
[engine-demotion] reason=hybrid-interp-splice detail=rt_stdin_read,rt_local_unix_close_v1,...
```

The list has 392 names. This is a **partial** demotion, not a module drop.
`run_file_jit` (`src/compiler_rust/driver/src/exec_core.rs`, the
`unresolvable_externs` block) finds every extern declaration whose name has no
symbol in the JIT symbol provider. It rewrites each call to that extern into an
`InterpCall` bridge, which the interpreter's extern table resolves by name at
run time. The rest of the module stays JIT-compiled. The cost is one
interpreter round-trip per call to these externs, plus the receipt naming the
splice.

## Breakdown (origin run)

| Class | Count | Examples |
|---|---|---|
| Win32 / Windows API names | 32 | `CreateProcessW`, `GetTickCount64`, `BCryptCreateHash`, `HeapAlloc` |
| other non-`rt_` names (`pmm_*`, `retained_native_*`, ...) | 11 | `pmm_alloc_page`, `retained_native_close` |
| foreign-platform `rt_*` (kqueue, iocp, event ports, arm, port I/O) | ~32 | `rt_kqueue_register`, `rt_iocp_poll`, `rt_event_ports_create`, `rt_port_outb` |
| host-applicable `rt_*` not registered in the JIT provider | ~317 | `rt_process_*` (76), `rt_simd_*` (57), `rt_linux_*` (25), `rt_http_*` (23), `rt_local_*` (18), `rt_file_*` (11, e.g. `rt_file_atomic_write`, `rt_file_modified`) |

## Fix directions (owner decision)

1. Register the host-applicable `rt_*` in the JIT symbol provider, either by
   adding them to the runtime symbol table or by checking that they are
   exported and `dlsym`-visible.
2. Cfg-prune the platform-foreign extern declarations from the host unit, so
   they are never declared and never spliced.

Neither is a by-name method dispatch or a cross-module link problem.

## Reproduce

```
SIMPLE_RUST_SEED_WARNING=0 <seed> run src/app/llm_caret/main.spl --help 2>&1 \
  | grep 'reason=hybrid-interp-splice' | sed 's/.*detail=//' | tr ',' '\n' | sort
```

## Classification of the 392 (2026-11-13, `origin/release/1.0.0` `5ed0d972afb`, aarch64 Linux)

Method. Ground truth is the linked seed, not a source grep:

- **(a)** = the name is a defined text symbol in the seed's runtime archives
  (`nm --defined-only` over `libsimple_runtime.a` + `libruntime_sffi_c.a` from the
  seed build). A source grep over-counts (it matches `#[cfg(test)]` twins in
  `process_observation_v4_twins.rs` and `extern` prototypes); `nm` of the final
  binary under-counts (unreferenced exports are dropped at link: 31 of 212).
- **(b)** = not (a), but the name is a key in the interpreter extern dispatch
  (`compiler/src/interpreter_extern/`).
- **(c)** = neither.

How the JIT resolves an extern: `run_file_jit` asks the symbol provider, which
only knows names that are in `RUNTIME_SYMBOL_NAMES`
(`src/compiler_rust/common/src/runtime_symbols.rs`) **and** that
`runtime/build.rs` found defined (Rust `#[no_mangle]` scan, or the C
`LINKED_C_SOURCES` scan). A resolved name with a `RuntimeFuncSpec`
(`compiler/src/codegen/runtime_sffi.rs`) is called with that exact signature; a
resolved name without one is imported with a uniform all-`I64` signature, which
is wrong for `f64` and leaves `bool`/`i32` returns with unspecified upper bits on
aarch64. So every registration below carries an exact spec.

| Class | Count | Sub-family | Count |
|---|---|---|---|
| (a) native symbol linked in the seed, not registered | 212 | Rust `#[no_mangle]` exports | 64 |
| | | C `rt_simd_*` (`runtime_simd_dispatch.c`, scan filtered to `rt_opencl_*`) | 55 |
| | | other C (`runtime_process_owned.c` + impl headers, `runtime_socket_nonblock.c`, `runtime_secure_staging.c`, time/memory TUs) | 93 |
| (b) interpreter handler only | 98 | Win32 API names | 32 |
| | | foreign-platform `rt_*` (kqueue, iocp, event ports, arm) | 23 |
| | | host-applicable | 43 |
| (c) no native symbol in the seed, no interpreter handler | 82 | defined only in a C TU the seed does not link | 50 |
| | | defined nowhere (`pmm_*`, `retained_native_*`, `rt_http_*`, `rt_ws_*`, arm dcache) | 32 |

62 of the 392 are already in `RUNTIME_SYMBOL_NAMES` and still unresolved, because
`build.rs` never sees their definition: `runtime_process_owned.c` is compiled into
the archive but is not in `LINKED_C_SOURCES`, and the `runtime_simd_dispatch.c`
scan keeps only `rt_opencl_*`.

143 of the 212 class (a) names also have an interpreter handler; 13 of the
wave 1 names have none, so before registration a JIT call to them failed at run
time (`declared in Simple but backed by no implementation`).

### (a) Rust exports
rt_arm_array_get_byte_u32, rt_arm_array_len_u32, rt_black_box, rt_debug_exit_success, rt_dyncall_4, 
rt_dyncall_5, rt_dyncall_6, rt_fd_stat_snapshot_v1, rt_file_atomic_write, rt_file_atomic_write_bytes_array, 
rt_file_atomic_write_mode, rt_file_mode, rt_file_modified, rt_file_modified_time, 
rt_heap_array_capacity_bytes, rt_heap_aux_live_bytes, rt_host_disk_headroom_bytes_v1, 
rt_io_file_meta_created, rt_io_file_meta_flags, rt_io_file_meta_modified, rt_io_file_set_permissions, 
rt_io_file_write, rt_io_file_write_all, rt_linux_container_user_close_v1, rt_linux_container_user_observe_v1, 
rt_linux_container_user_open_v1, rt_mem_attr_enabled, rt_par_atomic_i64_is_lock_free, rt_par_atomic_load_i64, 
rt_path_extension, rt_path_filename, rt_perf_dump_sdn, rt_print_err, rt_process_hwm_kib, 
rt_process_last_child_peak_rss_kib, rt_process_run_bounded_admitted_tuple_v1, rt_process_run_bounded_bytes, 
rt_process_run_bounded_environment_tuple_v1, rt_process_run_bounded_observed_tuple_v1, 
rt_process_run_bounded_tuple, rt_process_run_tuple, rt_process_spawn_async_environment_v1, rt_pty_close, 
rt_pty_is_running, rt_pty_read, rt_pty_resize, rt_pty_write, rt_random_randint, rt_random_uniform, 
rt_shell_exec, rt_stdin_read, rt_stdin_read_all, rt_string_from_byte_array, rt_string_to_byte_array, 
rt_tagged_add, rt_term_flush, rt_term_write, rt_text_validate_utf8, rt_transient_array_scope_identity_v1, 
rt_transient_array_scope_state_v1, spl_dlclose, spl_dlopen, spl_dlsym, spl_wffi_call_i64

### (a) C `rt_simd_*`
rt_simd_add_f32x4, rt_simd_add_f32x8, rt_simd_add_f64x4, rt_simd_add_i32x4, rt_simd_add_i32x8, 
rt_simd_add_i64x4, rt_simd_add_u32x4, rt_simd_add_u8x16, rt_simd_aes_round_last_u8x16, 
rt_simd_aes_round_u8x16, rt_simd_and_i32x4, rt_simd_and_i32x8, rt_simd_and_u32x4, rt_simd_and_u64x4, 
rt_simd_clmul_hi_u64, rt_simd_clmul_lo_u64, rt_simd_div_f32x4, rt_simd_div_f32x8, rt_simd_div_f64x4, 
rt_simd_fma_f32x4, rt_simd_fma_f32x8, rt_simd_fma_f64x4, rt_simd_hadd_f32x4, rt_simd_hmax_f32x4, 
rt_simd_hmin_f32x4, rt_simd_mul_f32x4, rt_simd_mul_f32x8, rt_simd_mul_f64x4, rt_simd_mul_i32x4, 
rt_simd_mul_i32x8, rt_simd_or_i32x4, rt_simd_or_i32x8, rt_simd_or_u32x4, rt_simd_or_u64x4, rt_simd_shl_i32x4, 
rt_simd_shl_i32x8, rt_simd_shl_u64x4, rt_simd_shr_i32x4, rt_simd_shr_i32x8, rt_simd_shr_u64x4, 
rt_simd_shuffle_u8x16, rt_simd_sub_f32x4, rt_simd_sub_f32x8, rt_simd_sub_f64x4, rt_simd_sub_i32x4, 
rt_simd_sub_i32x8, rt_simd_sub_i64x4, rt_simd_sub_u32x4, rt_simd_vec4u64_get, rt_simd_xor_i32x4, 
rt_simd_xor_i32x8, rt_simd_xor_u32x4, rt_simd_xor_u64x2, rt_simd_xor_u64x4, rt_simd_xor_u8x16

### (a) other C
rt_alloc_probe_count_v1, rt_alloc_probe_coverage_v1, rt_alloc_probe_reset_v1, rt_file_create_excl, 
rt_file_publish_noreplace, rt_file_sync, rt_hosted_select_surface, rt_host_memory_headroom_bytes_v1, 
rt_linux_group_available_capacity_v1, rt_linux_group_cancel_v1, rt_linux_group_collected_stream_v2, 
rt_linux_group_collect_v1, rt_linux_group_launch_broker_v1, rt_linux_group_launch_stream_broker_profiled_v3, 
rt_linux_group_launch_stream_broker_v2, rt_linux_group_parent_acquire_at_v2, 
rt_linux_group_parent_acquire_profiled_at_v3, rt_linux_group_parent_acquire_v1, 
rt_linux_group_parent_release_v1, rt_linux_group_poll_v1, rt_linux_group_start_stream_profiled_v3, 
rt_linux_group_start_stream_v2, rt_linux_group_start_v1, rt_linux_group_stream_admit_profiled_v3, 
rt_linux_group_stream_admit_v2, rt_linux_group_stream_collect_no_child_v2, 
rt_linux_group_stream_no_child_scope_v2, rt_linux_group_stream_recover_lease_v2, 
rt_linux_group_stream_release_inherited_v2, rt_linux_group_stream_verify_broker_profiled_v3, 
rt_local_unix_accept_v1, rt_local_unix_adopt_byte_endpoint_v1, rt_local_unix_claim_request_v1, 
rt_local_unix_close_v1, rt_local_unix_connect_v1, rt_local_unix_handoff_state_v1, 
rt_local_unix_listener_close_v1, rt_local_unix_listen_v1, rt_local_unix_peer_v1, rt_local_unix_poll_v1, 
rt_local_unix_read_handoff_now_v1, rt_local_unix_read_now_v1, rt_local_unix_read_v1, 
rt_local_unix_shutdown_write_v1, rt_local_unix_stage_stdout_v1, rt_local_unix_write_some_admitted_v1, 
rt_local_unix_write_some_now_v1, rt_local_unix_write_some_v1, rt_mem_guard_stats, rt_mem_harden_check_native, 
rt_process_inspection_v1_input_receipt_value, rt_process_inspection_v1_start_pinned_value, 
rt_process_observation_v4_ack_collect_value, rt_process_observation_v4_cancel_value, 
rt_process_observation_v4_capabilities_value, rt_process_observation_v4_close_cwd_value, 
rt_process_observation_v4_collect_value, rt_process_observation_v4_cwd_digest_value, 
rt_process_observation_v4_pin_cwd_value, rt_process_observation_v4_poll_value, 
rt_process_observation_v4_reserved_ack_value, rt_process_observation_v4_reserved_confirm_release_value, 
rt_process_observation_v4_reserved_matches_value, rt_process_observation_v4_reserved_observe_value, 
rt_process_observation_v4_reserved_start_pinned_value, rt_process_observation_v4_reserved_state_value, 
rt_process_observation_v4_reserve_value, rt_process_observation_v4_start_pinned_value, 
rt_process_observation_v4_start_value, rt_process_observation_v5_reserved_start_admitted_value, 
rt_process_observation_v6_reserved_poll_launch_value, 
rt_process_observation_v6_reserved_start_deferred_admitted_value, rt_process_owned_v3_cancel_value, 
rt_process_owned_v3_capabilities_value, rt_process_owned_v3_collect_value, rt_process_owned_v3_input_value, 
rt_process_owned_v3_observation_value, rt_process_owned_v3_poll_value, rt_process_owned_v3_release_value, 
rt_process_owned_v3_result_value, rt_process_owned_v3_set_capture_limits_value, 
rt_process_owned_v3_start_pinned_value, rt_process_owned_v3_start_value, rt_process_pin_executable, 
rt_process_run_owned_observed_bounded_value, rt_remove, rt_secure_temp_dir, rt_secure_temp_dir_make, 
rt_secure_temp_dir_set_parent, rt_secure_temp_dir_set_prefix, rt_time_now_seconds, rt_time_now_seconds_f64, 
spl_thread_current_id

### (b) Win32
AssignProcessToJobObject, BCryptCloseAlgorithmProvider, BCryptCreateHash, BCryptDestroyHash, 
BCryptFinishHash, BCryptHashData, BCryptOpenAlgorithmProvider, CloseHandle, CreateFileW, CreateJobObjectW, 
CreateProcessW, DeleteProcThreadAttributeList, GetExitCodeProcess, GetFileInformationByHandleEx, 
GetLastError, GetModuleFileNameW, GetProcessHeap, GetSystemTimes, GetTickCount64, GlobalMemoryStatusEx, 
HeapAlloc, HeapFree, InitializeProcThreadAttributeList, QueryInformationJobObject, ReadFile, ResumeThread, 
SetInformationJobObject, Sleep, TerminateJobObject, TerminateProcess, UpdateProcThreadAttribute, 
WaitForSingleObject

### (b) foreign-platform
rt_arm_elf64_entry, rt_arm_elf64_pt_load_align, rt_arm_elf64_pt_load_count, rt_arm_elf64_pt_load_filesz, 
rt_arm_elf64_pt_load_flags, rt_arm_elf64_pt_load_memsz, rt_arm_elf64_pt_load_offset, 
rt_arm_elf64_pt_load_vaddr, rt_event_ports_close, rt_event_ports_create, rt_event_ports_deregister, 
rt_event_ports_poll, rt_event_ports_register, rt_iocp_close, rt_iocp_create, rt_iocp_deregister, 
rt_iocp_poll, rt_iocp_register, rt_kqueue_close, rt_kqueue_create, rt_kqueue_deregister, rt_kqueue_poll, 
rt_kqueue_register

### (b) host-applicable
rt_browser_renderer_sandbox_enter, rt_browser_renderer_spawn_sandboxed, rt_call_ptr_0, rt_call_ptr_1, 
rt_call_ptr_2, rt_call_ptr_3, rt_current_time_ms, rt_entropy_hardware_ready, rt_fd_close, rt_fd_read_until, 
rt_fd_write, rt_file_list_dir, rt_fs_read_text, rt_get_concurrent_backend, rt_host_commit_headroom_bytes_v1, 
rt_hostname, rt_http_get, rt_http_request, rt_http_request_v2, rt_list_dir_recursive, rt_mkdir, 
rt_process_close_piped, rt_process_is_alive, rt_process_piped_exit_status_value, rt_process_read_stdout, 
rt_process_spawn_piped, rt_process_spawn_session_value, rt_process_stdout_state, rt_process_write_stdin, 
rt_process_write_stdin_some, rt_readdir, rt_readdir_count, rt_readdir_entry, rt_readdir_free, 
rt_simd_bytes_equal_span, rt_simd_find_byte_span, rt_stdin_read_line, rt_text_count_codepoints_cached, 
rt_text_is_ascii, rt_time_format, serial_println, spl_thread_sleep, unsafe_addr_of

### (c) C definition in a TU the seed does not link
rt_eprintln, rt_file_write, rt_hosted_safe_artifact_bundle3_identity_v1, 
rt_hosted_safe_artifact_bundle_n_finish_v1, rt_hosted_safe_artifact_bundle_n_identity_v1, 
rt_http_client_create, rt_http_client_destroy, rt_http_client_request, rt_http_client_set_timeout, 
rt_http_download, rt_path_normalize, rt_port_inb, rt_port_inl, rt_port_inw, rt_port_io_wait, rt_port_outb, 
rt_port_outl, rt_port_outw, rt_process_byte_endpoint_state_v1, rt_process_close_byte_endpoint_v1, 
rt_process_close_pinned_executable, rt_process_close_piped_ref_v1, rt_process_is_piped_alive_ref_v1, 
rt_process_piped_pid_for_generation_v1, rt_process_read_byte_endpoint_v1, rt_process_read_stdout_owned_v2, 
rt_process_read_stdout_ref_v1, rt_process_spawn_pinned_piped, rt_process_spawn_piped_generation_v1, 
rt_process_stdout_state_owned_v2, rt_process_stdout_state_ref_v1, rt_process_stream_abandon_unlaunched_v2, 
rt_process_stream_bind_v2, rt_process_stream_pid_v2, rt_process_stream_reserve_v2, 
rt_process_stream_retire_v2, rt_process_validate_byte_endpoint_v1, rt_process_validate_piped_owned_v2, 
rt_process_validate_piped_ref_v1, rt_process_write_stdin_some_owned_v2, rt_process_write_stdin_some_ref_v1, 
rt_read_cr3_raw, rt_retained_private_credential_close_v1, rt_retained_private_credential_error_v1, 
rt_retained_private_credential_open_v1, rt_retained_private_credential_publish_v1, 
rt_retained_private_credential_read_v1, rt_retained_private_credential_state_v1, rt_sleep_nanos, 
rt_write_cr3_raw

### (c) defined nowhere
pmm_alloc_page, pmm_alloc_page_raw, pmm_free_page, pmm_free_page_raw, pmm_ref_page, pmm_unref_page, 
retained_native_close, retained_native_read, retained_native_write, rt_arm32_dcache_clean_range, 
rt_arm32_dcache_invalidate_range, rt_arm64_dcache_clean_range, rt_arm64_dcache_invalidate_range, 
rt_http_client_set_header, rt_http_delete, rt_http_head, rt_http_patch, rt_http_post, rt_http_put, 
rt_http_server_create, rt_http_server_destroy, rt_http_server_route, rt_http_server_start, 
rt_http_server_static, rt_http_server_stop, rt_http_upload, rt_http_url_decode, rt_http_url_encode, 
rt_ws_close, rt_ws_connect, rt_ws_receive, rt_ws_send

## Wave 1 — 48 Rust exports registered (2026-11-13)

Manifest entry + exact `RuntimeFuncSpec` each; signatures transcribed from the
`#[no_mangle] extern "C"` definitions and checked against every `.spl`
declaration.

rt_arm_array_get_byte_u32, rt_arm_array_len_u32, rt_debug_exit_success, rt_fd_stat_snapshot_v1, 
rt_file_atomic_write_bytes_array, rt_file_mode, rt_file_modified, rt_file_modified_time, 
rt_heap_array_capacity_bytes, rt_heap_aux_live_bytes, rt_io_file_meta_created, rt_io_file_meta_flags, 
rt_io_file_meta_modified, rt_io_file_set_permissions, rt_io_file_write, rt_io_file_write_all, 
rt_mem_attr_enabled, rt_par_atomic_i64_is_lock_free, rt_par_atomic_load_i64, rt_path_extension, 
rt_path_filename, rt_print_err, rt_process_hwm_kib, rt_process_last_child_peak_rss_kib, 
rt_process_run_bounded_admitted_tuple_v1, rt_process_run_bounded_environment_tuple_v1, 
rt_process_run_bounded_observed_tuple_v1, rt_process_run_bounded_tuple, rt_process_run_tuple, 
rt_process_spawn_async_environment_v1, rt_pty_read, rt_pty_resize, rt_random_randint, rt_random_uniform, 
rt_shell_exec, rt_stdin_read, rt_stdin_read_all, rt_string_from_byte_array, rt_string_to_byte_array, 
rt_term_flush, rt_term_write, rt_text_validate_utf8, rt_transient_array_scope_identity_v1, 
rt_transient_array_scope_state_v1, spl_dlclose, spl_dlopen, spl_dlsym, spl_wffi_call_i64

Measured with the seed built from this change (sha256 `8532f7b39b025ad2…`) against
the base seed (`0ddf581b68c2f6cf…`), caret `--help`, 3 serial runs each:

| | splice names | wall (median) | peak RSS (median) | stdout vs interpreter |
|---|---|---|---|---|
| base | 392 | 7.05 s | 1,588 MB | byte-identical |
| wave 1 | 344 | 6.86 s | 1,589 MB | byte-identical |

Pinned by `src/compiler_rust/driver/tests/jit_extern_native_link_tests.rs` (3 of 4
red on the base seed, 4 of 4 green; the unknown-extern fail-closed test is green
on both).

Found while probing: the spliced path returned a wrong value for an `f64`
extern (`rt_random_uniform(2.5, 2.5)` printed a denormal under the JIT, `2.5`
under the interpreter). Native linking with the `F64` spec fixes it.

Class (a) Rust exports deliberately **left spliced**:

| Name | Reason |
|---|---|
| `rt_host_disk_headroom_bytes_v1` | native `statvfs` and the interpreter's `platform::disk_headroom` disagree (`/tmp`: native > 0, interpreter <= 0); owner must pick one |
| `rt_pty_close`, `rt_pty_is_running`, `rt_pty_write` | Rust returns a tagged `RuntimeValue`, `.spl` declares `-> bool` (raw) |
| `rt_file_atomic_write`, `rt_file_atomic_write_mode` | Rust returns `i64`, `.spl` declares `-> bool` |
| `rt_black_box` | `.spl` return is `i64?` |
| `rt_perf_dump_sdn` | native has no perf-region recorder; only the interpreter records |
| `rt_linux_container_user_{open,observe,close}_v1` | Rust definitions are `-95` stubs |
| `rt_tagged_add` | declared with `RuntimeValuePtr` parameters; not checked against the JIT value representation |
| `rt_dyncall_4/5/6` | all-`i64` Rust ABI, but the `.spl` declaration was not located; register once it is read |
| `rt_process_run_bounded_bytes` | (ptr, len) text ABI; needs the text-expansion path verified |
| `rt_process_stdout_state`, `rt_process_piped_exit_status_value` | `piped_process_observer.rs` is not compiled into the seed (not class (a); link fails) |

## Wave 2 — 19 scalar-ABI C exports registered (2026-11-13)

rt_alloc_probe_count_v1, rt_alloc_probe_coverage_v1, rt_alloc_probe_reset_v1, rt_file_create_excl, rt_file_sync,
rt_linux_group_cancel_v1, rt_linux_group_parent_release_v1, rt_linux_group_stream_release_inherited_v2,
rt_mem_guard_stats, rt_mem_harden_check_native, rt_process_observation_v4_close_cwd_value,
rt_process_observation_v4_reserve_value, rt_process_observation_v4_reserved_confirm_release_value,
rt_process_observation_v4_reserved_matches_value, rt_process_observation_v4_reserved_state_value,
rt_process_owned_v3_release_value, rt_time_now_seconds, rt_time_now_seconds_f64, spl_thread_current_id

Mechanism: `runtime/build.rs` gains `JIT_SCALAR_C_EXPORTS`, an allowlisted scan
(Linux only, a name registers only if its definition is found) of the TUs that
are compiled into the seed archive but not scanned wholesale. The TUs stay out
of `LINKED_C_SOURCES` on purpose: most of their exports take `const char*`
text or return an owned `SplArray*` that the interpreter handler adapts (nil
check, free, array -> tuple), so a direct JIT call is not equivalent.

| | splice names | wall (median) | peak RSS (median) | stdout vs interpreter |
|---|---|---|---|---|
| wave 1 seed `8532f7b39b025ad2…` | 344 | 7.03 s | 1,588 MB | byte-identical |
| wave 2 seed `5ff721a25c34d587…` | 325 | 7.07 s | 1,588 MB | byte-identical |

Test: two wave-2 cases in `jit_extern_native_link_tests.rs`, red on the wave 1
seed, green on the wave 2 seed (6 of 6).

Found while probing: the interpreter handler for the `rt_process_observation_v4_reserved_*`
family refuses by design (`process observation V4 is unavailable in interpreter
mode; use the exact native V4 provider`), so a spliced JIT call could never
succeed. Native linking is the only working lane for them.

## Remaining after wave 2: 325

| Group | Count | What it needs |
|---|---|---|
| class (a) C `rt_simd_*` | 55 | handle-based `int64_t` vector ABI in `runtime_simd_dispatch.c`; `build.rs` filters that TU to `rt_opencl_*` deliberately and the Rust runtime carries scalar-argument twins of the same names. Owner decision on which ABI the JIT struct values match |
| class (a) other C, text/array ABI | ~73 | `const char*` / (ptr, len) text expansion entries in `codegen/instr/calls.rs` plus a native equivalent of the interpreter's `take` adaptation for `SplArray*` returns (`rt_local_unix_*`, `rt_linux_group_*`, `rt_process_observation_v4_*`, `rt_process_owned_v3_*`) |
| class (a) Rust, non-exact ABI | 16 | listed under wave 1 |
| class (a) `rt_process_observation_v6_reserved_poll_launch_value` | 1 | scalar ABI, but `c_function_definitions` does not find its definition in `runtime_process_owned.c` |
| class (b) | 98 | 55 are Win32 or foreign-platform names: cfg-prune the declarations from the host unit. 43 host-applicable ones need a native provider |
| class (c) | 82 | no implementation in the seed; cfg-prune or implement |

Zero splice for caret `--help` therefore needs cfg-pruning of the platform-foreign
and unimplemented declarations (about 180 names), not more registration.

## Verification notes and follow-ups (2026-11-13)

- **Interpreter drift ratchet.** `extern_dispatch_covers_declared_runtime_symbols_with_live_callers`
  (`interpreter_extern/extern_drift_tests.rs`) requires every manifest name with a
  live `.spl` caller to have an interpreter handler. 19 of the registered names
  never had one (16 from wave 1, 3 from wave 2), so wave 1 turned that unit test
  red on `release/1.0.0`; wave 2 adds them to `ALLOWED_KNOWN_GAPS` with reasons.
  Interpreter behaviour is unchanged (a call failed closed before and still
  does). Writing real handlers for the cheap ones (`rt_path_extension`,
  `rt_path_filename`, `rt_term_write`, `rt_term_flush`, `rt_stdin_read*`) would
  remove them from that list.
- **Invalid-fd divergence, pre-existing family behaviour.** For `rt_io_file_*`
  the interpreter handler raises `argument 0 must be a valid file descriptor`,
  the native export returns `false`/`0`. The already-registered sibling
  `rt_io_file_flush(-1)` behaves the same way on the base seed, so the newly
  registered `rt_io_file_set_permissions` / `rt_io_file_meta_*` /
  `rt_io_file_write*` follow the family, not a new rule.
- **Probed under JIT and interpreter:** file mtime/mode, byte-array/text
  round-trip, UTF-8 validation, random int/f64, stderr print, shell exec, memory
  counters, time (i64 and f64), thread id, `rt_file_sync`, `rt_file_create_excl`,
  `rt_pty_resize` (i32 parameters), `rt_file_atomic_write_bytes_array`,
  `rt_pty_read`. **Probed under JIT only** (no interpreter handler, or handler
  refuses): path extension/filename, term write/flush, stdin readers,
  `rt_io_file_set_permissions` (bool parameter), V4 reserved scalars, alloc
  probes, linux-group scalars.
- **Registered but not probed:** `rt_process_run_tuple`,
  `rt_process_run_bounded_tuple`, `rt_process_run_bounded_*_tuple_v1`,
  `rt_process_spawn_async_environment_v1` (raw pointer/tuple ABI),
  `rt_io_file_write`, `rt_io_file_write_all`, `rt_io_file_meta_created/flags`,
  `rt_fd_stat_snapshot_v1`, `rt_par_atomic_*`, `spl_dlopen/dlsym/dlclose`,
  `spl_wffi_call_i64`, `rt_arm_array_*`, `rt_debug_exit_success`,
  `rt_process_observation_v4_reserve_value`, `rt_linux_group_stream_release_inherited_v2`.
- **Declarations are unconditional.** The platform-foreign names are declared
  with no `@cfg` in `src/lib/nogc_sync_mut/io/windows_process_owner_abi.spl`
  (Win32), `src/lib/nogc_async_mut/io/platform_event.spl` (kqueue/iocp/event
  ports) and `src/os/kernel/arch/**` (`pmm_*`, `rt_port_*`). `run_file_jit`
  lists every declared extern without a symbol, whether or not any MIR `Call`
  targets it, while `apply_hybrid_transform` only rewrites `Call` instructions.
  The cheapest next step is seed-side: in
  `src/compiler_rust/driver/src/exec_core.rs` (the `unresolvable_externs`
  block), keep only names that are a `Call` target or `GlobalLoad` name in the
  lowered MIR. That removes declared-but-never-called names from the receipt
  without touching `.spl`.
- `scripts/check/check-jit-runtime-symbol-manifest.shs` is red on the base and
  names `rt_file_atomic_write`, `rt_file_atomic_write_mode`, `rt_perf_dump_sdn`
  and `rt_process_run_bounded_bytes` as codegen-emitted and missing from the
  manifest. They are the ones left spliced above; settle their ABI questions
  and that gate's list shrinks with them.
- `bug_db.sdn` rows for this bug were not updated; the bug stays OPEN.
