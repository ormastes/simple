# `skip(name, reason)` called inside an `it` body is dropped and the example reports as passed

Status: open, confirmed on a real run. Not fixed in lane L5 (runner code is out
of scope there).

## Symptom

`test/03_system/lib/slang/feature/slang_tts_live_spec.spl` run 4 (2026-11-19,
release seed `C:/dev/seeds/simple-release.exe`): `C:/dev/model` had been
deleted, so the gate took its `skip(...)` + `return` path. The runner printed

```
  ✓ synthesizes a sentence that ASR hears back
SPEC FILE VERDICT: ... outcome=OK declared>=1 executed=1 passed=1 failed=0 skipped=0
```

Nothing ran (no wav written, ~1 min instead of ~5), yet the verdict is a pass
with `skipped=0`. Log: `C:/dev/slang-logs/l5/tts_live_run4.log`.

## Where

`src/lib/nogc_sync_mut/spec.spl`:

- `skip()` (line ~651) is a DECLARATION, a sibling of `it`, not a statement for
  use inside an example body.
  - Aggregate mode: it calls `_aggregate_declare` (line ~147), which returns ""
    while `_aggregate_in_test` is set ("case declared from test or hook
    callback"), and `skip` then returns without counting anything.
  - Plain mode: `_run_test("skipped")` (line ~322) is false unless the filter is
    `skipped`, so it returns before `test_skipped` is incremented.
- `_execute_it` (line ~384) then sees `current_test_errors.len() == 0` and no new
  `pending`, and records the enclosing example as `pass` (line ~431).

So every gated spec of the shape

```
it "does the live thing":
    if not _live_enabled():
        skip("does the live thing", "needs ...")
        return
    ...
```

reports a pass when its gate is closed. `pending(reason)` inside a body is
counted correctly (the `test_pending > pending_before` branch). That is the
existing in-body primitive.

## Affected files (candidates)

`grep -rlE '^ {8,}(skip|_skip)\(' test --include=*.spl` = 73 files. Indentation of
8 or more columns means the call sits inside an example body (`describe` at 0,
`it` at 4). None defines its own `fn skip(`. Wrappers named `_skip` that end in
`skip()` are included. Each file still needs a per-call check; a few calls may
be in helpers that are never called from an example.

- `test/01_unit/app/build/clang_policy/native_ninja_controller_spec.spl`
- `test/01_unit/app/build/clang_policy/native_rebuild_barrier_spec.spl`
- `test/01_unit/browser_engine/fractional_advance_accumulation_spec.spl`
- `test/01_unit/lib/gc_async_mut/slang/model_executor/pure/tokenizer_spec.spl`
- `test/01_unit/lib/nogc_sync_mut/sffi/isa_feature_readback_spec.spl`
- `test/01_unit/lib/nogc_sync_mut/text_layout/advance_staging_pen_drift_spec.spl`
- `test/01_unit/lib/nogc_sync_mut/trace/xray_native_inprocess_patch_spec.spl`
- `test/01_unit/lib/runtime_family_forbidden_import_guard_spec.spl`
- `test/02_integration/app/bootstrap_builder/worker_execution_spec.spl`
- `test/02_integration/app/bootstrap_builder/worker_timeout_cleanup_spec.spl`
- `test/02_integration/app/bug_add_database_preservation_spec.spl`
- `test/02_integration/app/cli_debug_probe_live_context_spec.spl`
- `test/02_integration/app/devhub/messenger/devhub1_oss_interop_spec.spl`
- `test/02_integration/app/feature_gen_log_modes_spec.spl`
- `test/02_integration/app/mcpgdb_log_modes_spec.spl`
- `test/02_integration/app/pkg_manifest_write_spec.spl`
- `test/02_integration/app/portal/portal_server_spec.spl`
- `test/02_integration/app/scv_db_local_store_it_spec.spl`
- `test/02_integration/app/scv_db_offline_actor_it_spec.spl`
- `test/02_integration/app/scv_db_quarantine_store_it_spec.spl`
- `test/02_integration/app/scv_event_journal_spec.spl`
- `test/02_integration/app/scv_jj_mutating_adapter_spec.spl`
- `test/02_integration/app/scv_mvp_spec.spl`
- `test/02_integration/app/sj_daemon_mutual_exclusion_spec.spl`
- `test/02_integration/app/spec_coverage_log_modes_spec.spl`
- `test/02_integration/app/test_runner_cached_discovery_prefix_spec.spl`
- `test/02_integration/app/tooling/centralized_storage_roots_spec.spl`
- `test/02_integration/app/ui_access_sqlite_demand_rejection_spec.spl`
- `test/02_integration/app/ui_access_sqlite_provider_spec.spl`
- `test/02_integration/bootstrap/macos_process_live_spec.spl`
- `test/02_integration/bootstrap/macos_process_live_tmpdir_expansion_spec.spl`
- `test/02_integration/bootstrap/stage2_object_path_diagnostic_read_spec.spl`
- `test/02_integration/compiler/backend/cranelift_arithmetic_spec.spl`
- `test/02_integration/compiler/backend/cranelift_narrow_cast_spec.spl`
- `test/02_integration/compiler/backend/gnu_runtime_owner_index_spec.spl`
- `test/02_integration/compiler/backend/guarded_optional_reference_native_spec.spl`
- `test/02_integration/compiler/backend/llvm_env_get_local_owner_native_spec.spl`
- `test/02_integration/compiler/backend/optional_collection_provenance_native_spec.spl`
- `test/02_integration/compiler/frontend_offload_driver_spec.spl`
- `test/02_integration/gpu/engine2d_vulkan_damage_scoped_mirror_spec.spl`
- `test/02_integration/gpu/engine2d_vulkan_readback_unpack_cost_spec.spl`
- `test/02_integration/io/external_file_io_spec.spl`
- `test/02_integration/io/external_text_io_spec.spl`
- `test/02_integration/io/file_handle_nullable_read_spec.spl`
- `test/02_integration/io/file_text_session_spec.spl`
- `test/02_integration/io/sosix_stdin_session_spec.spl`
- `test/02_integration/io/sosix_tool_text_spec.spl`
- `test/02_integration/lib/io/process_observation_hal_capabilities_v4_spec.spl`
- `test/03_system/acceptance/gpu_tutorial_curriculum_acceptance_spec.spl`
- `test/03_system/app/build/feature/dist_build_staged_two_node_spec.spl`
- `test/03_system/app/build/feature/dist_build_two_node_spec.spl`
- `test/03_system/app/buildrunner/feature/hello_buildrunner_acceptance_spec.spl`
- `test/03_system/app/hardware/feature/kv260_simpleos_boot_silicon_spec.spl`
- `test/03_system/check/simpleos_kernel_fabricated_rt_symbol_guard_spec.spl`
- `test/03_system/lib/slang/feature/slang_caret_local_usage_spec.spl`
- `test/03_system/lib/slang/feature/slang_gpu_offload_live_spec.spl`
- `test/03_system/lib/slang/feature/slang_http_server_live_spec.spl`
- `test/03_system/lib/slang/feature/slang_kv_cache_live_exact_output_spec.spl`
- `test/03_system/lib/slang/feature/slang_kv_cache_live_spec.spl`
- `test/03_system/lib/slang/feature/slang_model_variety_live_spec.spl`
- `test/03_system/lib/slang/feature/slang_multimodal_live_spec.spl`
- `test/03_system/lib/slang/feature/slang_openai_conformance_in_development_spec.spl`
- `test/03_system/lib/slang/feature/slang_openai_conformance_live_spec.spl`
- `test/03_system/lib/slang/feature/slang_pooling_live_spec.spl`
- `test/03_system/lib/slang/feature/slang_pure_kv_cache_spec.spl`
- `test/03_system/lib/slang/feature/slang_pure_rocm_generate_spec.spl`
- `test/03_system/lib/slang/feature/slang_pure_sampling_spec.spl`
- `test/03_system/lib/slang/feature/slang_runner_dispatch_live_spec.spl`
- `test/03_system/lib/slang/feature/slang_tts_live_spec.spl`
- `test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl`
- `test/03_system/runtime/sosix_host_runtime_access_spec.spl`
- `test/03_system/tools/llm/slang_local_model_root_hello_spec.spl`
- `test/fixtures/spec_aggregate_registry/main.spl`

## Fix options (owner decision)

1. Make `skip()` called from inside a running example mark that example
   skipped: count `test_skipped`, and have `_execute_it` return "skip", like the
   pending branch.
2. Or reject it loudly, failing with "skip() inside an example; use pending()
   or a skip_if decorator", and migrate the files above.

Lane L5's spec writes a `SKIPPED:` line to its own record file as a stopgap
(commit dab01a0415a on `work/slang-l5-tts-20261117`).

## Rust seed fix (lane skipfix, 2026-11-23)

Option 1, in the seed's BDD handler (`src/compiler_rust/compiler/src/interpreter_call/bdd.rs`):

- New thread-local `BDD_SKIP_IN_IT`, reset when an `it` starts and in `clear_bdd_state`.
- The `skip` builtin arm: when called while an `it` body runs (`BDD_INSIDE_IT`), it sets the
  flag instead of being left alone. At describe level behaviour is unchanged
  (`record_describe_level_skip`).
- The `it` arm: if the flag is set, the example is recorded skipped
  (`BDD_IGNORED_TESTS`, `record_test_result(..., true, true)`) and printed
  `○ <name> (skip in body)`. Skip wins over a later failing expect or error.
  The Simple `skip()` body still prints its own `skipped (<reason>)` line, which the
  runner's `Results:` counter reads, so the new marker is worded not to count twice.

Tests (fail on old code, pass on new):

- Rust: `skip_in_example_tests` in bdd.rs (2 tests; `cargo test` log
  `C:/dev/slang-logs/skipfix/cargo_test2.log`, 2 passed).
- Spec: `test/01_unit/lib/spec/skip_in_it_body_spec.spl` (1 real pass, 2 in-body skips, one
  followed by a failing expect). Old seed: `passed=2 failed=1 skipped=0`
  (`new_spec_pinned_seed.log`). Fixed seed: `passed=1 failed=0 skipped=2`
  (`final_spec.log`).

Open: the deployed `C:/dev/seeds/simple-release.exe` and the pure-Simple runner
(`spec.spl`, handled by the skipfix-spl lane) do not have this fix until redeployed;
the 73 files above still rely on their `SKIPPED:` stopgap lines until then.

## Pure-Simple fix (lane skipfix-spl, 2026-11-23)

Option 1 is done in `src/lib/nogc_sync_mut/spec.spl`: `skip()` called while an example runs records it, and `_execute_it` returns "skip" and counts `test_skipped` (skip wins over a later pass or fail). Pinned by `test/01_unit/lib/nogc_sync_mut/spec_skip_in_body_spec.spl`, which drives `_execute_it` directly: on the old code 2 of 3 examples fail ("expected pass to equal skip"), on the new code 3 of 3 pass.

The seed's native `it` (bdd.rs, section above) never goes through `_execute_it`, so this test drives it directly.
