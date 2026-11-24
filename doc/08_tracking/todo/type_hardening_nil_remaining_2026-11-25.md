# Type hardening: nil / unit / enum work remaining (2026-11-25)

Campaign on `release/1.0.0`: no primitives on public APIs (`text` exempt), `nil` only
inside `unsafe`, optionals use `T? = None` / `.is_none()` / `.is_some()`. Option
elimination and nil→error escalation come later.

Conversion rule for all nil items: convert only provable Options (declared `T?`,
result of a fn `-> T?`, later `.unwrap()`ed). Leave extern / `rt_*` results, slot
tables, `-> Nil`, `Ok(nil)`, untyped values. In the interpreter `None == nil` is
true, so a correct conversion is behaviour-neutral; `to_be_nil()` fails on `None`.

Landed so far: #11191 #11248 #11262 #11263 #11311 #11317 #11320 #11323 #11325
#11326 #11329 #11331 #11336 #11308.

## Priority: seed SPL-UNIT-002 widening
- Branch `work/seed-unit-widen-20261124` (origin @ `7ed07d14846`), unverified WIP:
  widens unit tracking to fields, methods, lambdas, named args
  (`src/compiler_rust/compiler/src/hir/lower/`), +153 lines of Rust tests.
- Run `cargo check --release --bin simple` and `cargo test` for the compiler crate,
  then the SPL-UNIT-002 `.spl` specs before/after.
- Census new violations in `src/lib` / `src/app`; fix trivial ones or demote the
  new cases to warn. Then open a PR.
- Add `to_be_some` and the negated form to the Rust seed spec interpreter, with a spec.

## src/compiler nil
- Only the `25.traits` safe auto-fix landed (#11320). Hand conversion is left in 25.traits.
- Not started in the other layers: 00.common, 10.frontend, 15.blocks, 20.hir, 30.types,
  35.semantics, 50.mir, 55.borrow, 60.mir_opt, 70.backend, 80.driver, 85.mdsoc,
  90.tools, 95.interp, 99.loader. Each needs the safe auto-fix, then hand conversion.

## src/app nil (hand conversion)
- `build` / `bootstrap_builder`: #11316 still open; it needs a rebase and a gate run.
- Branch `work/nil-app-g3b-20261124` covers `test_audit..wm_compare`: 130 sites in
  40 files, specs not run yet. Run `async_web_spec`, `host_gui_device_scale_spec` and
  `backend_measurement_retained_switch_spec`, then open the PR.
- `office` has ~139 sites:
  - Convertible: `parse_cell_ref`, `parse_range`, `zip_extract`, `current_slide`,
    `_validation_find_rule`, `fill_series`, and `cells.get` / `d.get`.
  - Leave: `file_read_bytes`, `rt_stdin_read_line`, `text.to_int()`.
- `io` has 29 sites:
  - Convertible: `file_hash_sha256`, `env_get_opt`, `stdin_read_line`,
    `collection_capture_finish`, `try_parse_int`, `_nb_path_absolute_raw`.
  - Leave: `rt_*`, `sys_get_args`, `env_get`.
- `llm_caret`, `image_to_markdown`, `lint`, `mcp` have ~85 sites: convert json results
  and `_ws_pane`; leave `input()`.
- `llm_dashboard`: `event_to_activity_entry`, `get_agent`, `try_parse_int`.
- `orchestrator`:
  - `host_identity_exchange_v1` 173-174
  - `host_identity_profile_v1` 110/121/175
  - `host_primary_service_v5` 25/28
  - `server_ssh_transport_v1` 71/116
- To check first: `optimize` line 220 and `game.breakout` lines 178/195.
- `itf`: ~25 `any`-typed sites; they need typing first.
- `try_recv` channel results (15 sites in ui.web / ui.browser / ui.tui_web): check
  whether `try_recv` returns an Option.
- ~600 sites the agents could not prove optional (field types not visible from the file,
  sentinels such as editor `active_buffer()`).
- Dropped as unverified: `dashboard/assistant_import.spl` and
  `assistant_collectors_text_json.spl`.
- `compiler_entrypoint/inventory_scratch.spl` is blocked:
  `compiler_inventory_checked_read_spec` uses `to_be_nil()`.
- Audit two things in the landed conversions: chained-call locals that were judged by
  the first call's type only, and `extern fn -> T?` results that were converted.
- `return nil` / `= nil` inside `-> T?` fns are not attempted yet.

## Spec asserts
- `test/01_unit`: 11 converted files were dropped because their specs failed differently
  from base. Re-run each on base and re-apply if it checks out:
  - `async_ui`
  - `jit_typed_ir_equivalence`
  - `facet_hir_codec_compat`
  - `enum_contract_hir_wiring`
  - `compositor_content_registry`
  - `host_compositor_entry`
  - `usb_hid_input_backend`
  - `ipc`
  - `reverse_reference_sort_equivalence`
  - `hir_codec_nonfatal_existing`
- ~485 `to_equal` nil asserts are not provable Options and need hand typing.
- Owner decision: are the ~140 `to_be(true|false)` nil asserts in scope?
- Outside `test/01_unit`:
  - Retry the 4 orchestrator specs and physical_vulkan_2d (ERROR executed=0; compare
    with base).
  - Look up the types of `sosix_tcp_*`, `showcase_hosts`, `db_sdn`,
    `retained_private_credential`, `structured_owner_task`, `library_mode_cache_io`.
- Delete the tracked stray file
  `test/01_unit/lib/common/text_layout/.spipe_cov_*_font_renderer_spec.spl`.
- `test/01_unit/compiler/driver/mir_shard_hir_residency_spec.spl` lines 212/216 were
  changed to `to_equal(1)` in #11325, but `mir_shard_pool_parallel_v1(0, ...)` returns 0.
  A fix PR has been requested.

## Code generators and GPU library
- `src/app/desugar/trait_desugar.spl:187,195` emits `return nil` / `nil` into an
  `Option<T>` fn. Emit `None` and update the goldens.
- `src/app/desugar/context_params.spl:102` emits `= nil`. Emit `None` when `T` is optional.
- `src/compiler/90.tools/sffi_gen/resource_wrapper_gen.spl:65` emits `nil` in a
  `-> Class?` factory. Emit `None`.
- Still to check: `wrapper_gen`, `spec_gen`, `feature_gen`, and the ffi/sffi templates.
- ~259 nil sites in `src/lib/gc_async_mut/{gpu,cuda,rocm,vulkan,torch}`: convert
  Option-only sites and leave handle externs alone.

## Bool flags → enums
- `src/lib/nogc_sync_mut/io/process_ops.spl` (the canonical copy): turn the `retire`
  and `pinned` flags into enums and update the callers.
- `env_detect` copies (`nogc_async_mut`, `gc_sync_mut`, `gc_async_mut`): turn the
  bools that select behaviour into enums.
- `src/app/wm_compare_host/process_ops.spl`: same as `process_ops`.

## Refactor auto-fix rules (opt-in)
- Safe rule: remove `pub` from a fn or field that exposes a primitive and has no users
  outside its module. Only apply it when the usage scan covers the whole repo.
- Suggestion only: propose a `unit` type for a class with exactly one primitive field.
- Wire both rules next to NIL-UNSAFE-001 in `src/app/io/cli_lint_commands.spl`, keep
  them out of the `registry.spl` defaults, and write specs modelled on
  `nil_unsafe_safe_fix_spec.spl`.

## Later
- Escalate NIL-UNSAFE-001 from warn to error once the counts above are near zero.
- Eliminate Option.
