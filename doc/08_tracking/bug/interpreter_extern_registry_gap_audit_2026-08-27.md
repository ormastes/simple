# Audit: native-codegen registry vs interpreter extern dispatch gap (2026-08-27)

Read-only audit. Nothing fixed. Worktree: detached `origin/main` @ `ed6545f2e3b`.

## Headline counts

| measure | count |
|---|---|
| Symbols registered for native codegen (`runtime_symbols.rs`) | **1852** |
| Registered but NOT reachable by any interpreter dispatch path | **754** |
| ...of those, declared `extern fn` somewhere in `src/lib/**` (LIVE) | **79** |
| ...remainder (latent — no `.spl` declaration in `src/lib`) | 675 |

Registered set measured as the union of the two arrays in
`src/compiler_rust/common/src/runtime_symbols.rs`:
`CORE_REQUIRED_RUNTIME_SYMBOLS` (line 118) and `RUNTIME_SYMBOL_NAMES` (line 385).

## Mechanism found in `interpreter_extern/` (step 2)

Dispatch is a **four-stage chain** in `interpreter_extern/mod.rs::dispatch_extern`
(entered from `interpreter_sffi.rs:783`, which routes any `rt_*`/`spl_*` name here):

1. **Static `HashMap<&'static str, ExternHandler>`** — `EXTERN_DISPATCH`
   (`mod.rs:52`), built by `init_dispatch_table()` (`mod.rs:252`). Rows are
   **string literals**, added either through the local `macro_rules! insert_simple!`
   (`mod.rs:254`) or bare `m.insert("name", ...)` for handlers needing `env`.
   Measured 2042 literal rows (includes non-`rt_` builtins such as `abs`, `ceil`).
2. **Wildcard prefix arms** — `name.starts_with("rt_sdl2_")`, `rt_glfw_`,
   `rt_sdl3_`, `rt_audio_` (minus `rt_audio_sdl2_`), `rt_fb_`, `rt_image_`,
   `rt_simpleos_log_`/`rt_log_target_`, `rt_opengl_`, `rt_oneapi_`, `rt_driver_`,
   `rt_vulkan_`, `rt_winit_`, `rt_rapier2d_`, `rt_host_gpu_lane_`,
   `rt_host_gpu_queue_` — each delegating to a per-family `dispatch(name, args)`
   that itself matches string literals. 30 prefixes counted (incl. nested winit ones).
3. **`capability_gap::matches`** — six families (`rt_webgpu_`, `rt_vk_`, `rt_gui_`,
   `rt_lyon_`, `rt_gamepad_`, `rt_hook_`) returning an honest family-named error
   rather than "unknown extern function".
4. **`dynamic_sffi::try_call_dynamic`** — a **dlopen fallback** against
   `libsimple_runtime.so`, then the generic `unknown extern function` error.

The extraction treated a name as handled if it is a table literal, a `"rt_x" =>`
match arm / `name == "rt_x"` test in any non-test code in `interpreter_extern/**`,
or covered by a stage-2 prefix. Zero of the 754 (and zero of the 79) fall in the
stage-3 capability-gap families.

## The dlopen caveat — measured, not assumed

Stage 4 means "absent from the static table" does not automatically mean "fails".
`load_runtime_library()` (`dynamic_sffi.rs:108`) searches only: the executable's
own directory, `../lib`, `target/{debug,release,bootstrap}/` relative to CWD, and
the system loader path. **No `libsimple_runtime.so` exists beside
`bin/release/x86_64-unknown-linux-gnu/simple`**, so on the deployed seed this
fallback is inert — confirmed empirically by the spot-checks below, where names
that the seed statically links internally (e.g. `rt_env_vars`, `rt_math_hypot`)
still failed. Under a layout where that .so *is* present, some of the 79 could
resolve dynamically; the 79 is therefore an **upper bound on live breakage for
that hypothetical layout, and an exact measurement for the deployed one**.

## Spot-checks (step 5) — observed output

Binary: `bin/simple` -> `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
60744944 bytes, mtime 2026-08-26 01:16:25 UTC. `--version` reports
`Simple Language v1.0.0-RC` and warns it is the Rust bootstrap seed.

Each spec: `use std.spec.step`, one `extern fn` re-declaration copied from
`src/lib`, one `it` block calling it. Run with `bin/simple test <file>`.

```
rt_process_run_owned_observed_bounded_value  ->  semantic: unknown extern function: rt_process_run_owned_observed_bounded_value
    SPEC FILE VERDICT: a_spec.spl outcome=ERROR executed=1 passed=0 failed=1   (rc=1)

rt_math_hypot                                ->  semantic: unknown extern function: rt_math_hypot
    SPEC FILE VERDICT: b_spec.spl outcome=ERROR executed=1 passed=0 failed=1   (rc=1)

rt_signal_check                              ->  semantic: unknown extern function: rt_signal_check
    SPEC FILE VERDICT: c_spec.spl outcome=ERROR executed=1 passed=0 failed=1   (rc=1)

rt_env_vars                                  ->  semantic: unknown extern function: rt_env_vars
    SPEC FILE VERDICT: d_spec.spl outcome=ERROR executed=1 passed=0 failed=1   (rc=1)
```

Negative control (a symbol that IS in the table, same harness):

```
rt_time_now_unix_micros
    SPEC FILE VERDICT: e_spec.spl outcome=OK executed=1 passed=1 failed=0      (rc=0)
```

So the failures are attributable to the missing registration, not to the harness.

## The 79 live names

- `rt_actor_recv`
- `rt_actor_spawn`
- `rt_actor_stop`
- `rt_actor_try_send`
- `rt_array_new_with_cap_bool`
- `rt_array_new_with_cap_i64`
- `rt_array_new_with_cap_js_value`
- `rt_atexit_check`
- `rt_atexit_install`
- `rt_atomic_bool_fetch_and`
- `rt_atomic_bool_fetch_not`
- `rt_atomic_bool_fetch_or`
- `rt_bdd_clear_state`
- `rt_bdd_expect_truthy`
- `rt_bdd_format_results`
- `rt_cli_dispatch_rust`
- `rt_cli_read_file`
- `rt_cli_run_brief`
- `rt_cli_run_fix`
- `rt_cli_run_lex`
- `rt_coverage_path_probe`
- `rt_cuda_event_elapsed_ms`
- `rt_cuda_launch_kernel_name`
- `rt_cuda_memcpy_dtoh_async`
- `rt_cuda_memcpy_htod_async`
- `rt_cuda_stream_create`
- `rt_cuda_stream_destroy`
- `rt_cuda_stream_synchronize`
- `rt_current_task_id`
- `rt_debug_add_breakpoint`
- `rt_debug_continue`
- `rt_debug_current_file`
- `rt_debug_current_line`
- `rt_debug_is_active`
- `rt_debug_locals`
- `rt_debug_pause`
- `rt_debug_remove_all_breakpoints`
- `rt_debug_remove_breakpoint`
- `rt_debug_set_active`
- `rt_debug_set_step_mode`
- `rt_debug_stack_depth`
- `rt_debug_stack_trace`
- `rt_dh_curve25519_free`
- `rt_dh_curve25519_keypair`
- `rt_dh_curve25519_public_key`
- `rt_dh_curve25519_shared_secret`
- `rt_ed25519_sign_seed`
- `rt_env_vars`
- `rt_madvise`
- `rt_math_fma`
- `rt_math_hypot`
- `rt_metal_buffer_download_raw`
- `rt_metal_buffer_upload_raw`
- `rt_metal_set_bytes_raw`
- `rt_mmap`
- `rt_msync`
- `rt_munmap`
- `rt_path_parent`
- `rt_print`
- `rt_process_run_owned_observed_bounded_value`
- `rt_process_run_with_limits`
- `rt_process_spawn`
- `rt_read_stdin_line`
- `rt_signal_check`
- `rt_signal_install`
- `rt_stdout_write`
- `rt_tls_client_read_checked`
- `rt_tls_client_read_timeout_checked`
- `rt_tls_get_cipher_suite`
- `rt_tls_get_negotiated_alpn`
- `rt_tls_is_handshake_complete`
- `rt_tls_server_accept`
- `rt_tls_server_close_connection`
- `rt_tls_server_create`
- `rt_tls_server_read_checked`
- `rt_tls_server_shutdown`
- `rt_tls_server_write`
- `rt_tls_server_write_bytes`
- `rt_write_fill_u32s_to_raw_checksum`

## What was measured vs inferred

- **Measured:** the two registered arrays; the literal/prefix handled set; the
  set difference; `extern fn` declarations under `src/lib/**` (`src/std` is a
  symlink to `src/lib`, so there is one tree, not two); five real `bin/simple test` runs.
- **Inferred / uncertain:**
  - The handled set is extracted by **regex over Rust source**, not by running
    the compiler. A handler registered by a shape the regexes miss (a computed
    name, a table built in another crate, a `match` arm formatted unusually)
    would be counted as unhandled — i.e. the 754 could be an **overcount**. The
    four spot-checks argue the overcount is not systematic, but only four names
    were verified out of 79.
  - Conversely, "reachable from `src/lib`" only looks at `src/lib/**`. Names
    declared `extern fn` under `src/app/**`, `src/compiler/**`, `src/os/**` or
    `test/**` are excluded, so **79 undercounts symbols that are live in practice**.
  - Some of the 675 latent names are deliberately unregistered kernel/baremetal
    symbols (e.g. `rt_mmio_*`, per the comment at `mod.rs` ~2930); they are not
    defects. No attempt was made to classify the 675.
  - Registered/handled counts are name-set only; **signature/arity agreement was
    not checked**. A name present in both registries can still misbehave.
