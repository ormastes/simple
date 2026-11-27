# Type hardening: nil / unit / enum work remaining (2026-11-25)

Campaign on `release/1.0.0`: no primitives on public APIs (`text` exempt), `nil` only
inside `unsafe`, optionals use `T? = None` / `.is_none()` / `.is_some()`. Option
elimination and nil→error escalation come later.

Conversion rule for all nil items: convert only provable Options (declared `T?`,
result of a fn `-> T?`, later `.unwrap()`ed). Leave extern / `rt_*` results, slot
tables, `-> Nil`, `Ok(nil)`, untyped values. In the interpreter `None == nil` is
true, so a correct conversion is behaviour-neutral; `to_be_nil()` fails on `None`.

Landed so far: #11191 #11248 #11262 #11263 #11308 #11311 #11317 #11320 #11323
#11325 #11326 #11329 #11331 #11336 #11384 #11388 #11391 #11394 #11397 #11399
#11400 #11408 #11409 #11411 #11413 #11416 #11420 #11423 #11425 #11426 #11427
#11428 #11429 #11430 #11431 #11432 #11437 #11438.

## Priority: seed SPL-UNIT-002 widening — DONE
- Landed in **#11388**: widened Rust seed `SPL-UNIT-002` tracking to struct/class
  fields, method calls, lambdas, and named args
  (`src/compiler_rust/compiler/src/hir/lower/`, 9 files + 153 lines of Rust tests),
  verified with `expression_tests` (82/82) and all 5 `SPL-UNIT-002` `.spl` specs
  (0 new violations on `src/lib/common/units` and `process_ops.spl`).
- `to_be_some` and statement-position `.not_()` BDD matchers landed concurrently on
  `release/1.0.0`.

## src/compiler nil — DONE (all 16 layers swept for provable Options)
- Front layers (`00.common`, `10.frontend`, `15.blocks`, `20.hir`, `25.traits`):
  **#11400**, **#11408**, **#11423** — **120 files**, 626 `nil` tokens converted;
  945 non-provable / formal-pinned (`hash_algorithm_registry_v1.spl`) /
  flat-AST slot-table / `# GENERATED` (`generated/hir_codec.spl`) / `@workaround`
  sites preserved.
- Mid layers (`30.types`, `35.semantics`, `50.mir`, `55.borrow`, `60.mir_opt`):
  **#11427**, **#11430**, **#11437** — **106 files**, 668 sites converted (+
  `byte_len()` fix in `switch_operators_calls.spl`); formal-pinned
  (`const_eval.spl`, `aspect_weave.spl`, `mir_aop_injection.spl`), `unsafe`
  audit-pinned (`mir_lowering_stmts.spl`), `# DESUGARED`, and non-optional checks
  preserved.
- Backend & tools (`70.backend`, `85.mdsoc`, `90.tools`, `95.interp`, `99.loader`):
  **#11426**, **#11428**, **#11429**, **#11431** — **159 files**, 878 sites
  converted; formal-pinned (`core_codegen.spl`), `rt_*` wrappers, `# DESUGARED`
  fields, `unsafe` / void stubs, and `lint_nil_unsafe.spl` test patterns preserved.
- Driver (`80.driver`): **#11425**, **#11432**, **#11438** — **139 files**, 759
  `nil` tokens converted; 119 tokens across 30 files preserved (5 formal-pinned
  cache/build files, `rt_*` wrappers, `Ok(nil)`, SFFI-audit pinned lines,
  `@workaround` guards, non-optional checks).

## src/app nil (hand conversion) — DONE for provable Options
- `test_audit..wm_compare` (`#11384`): **40 files**, 130 provable sites converted.
- Remaining cataloged `src/app/` dirs (`#11397`, `#11413`, `#11416`): **94 files**,
  388 provable sites converted across `office`, `io`, `llm_dashboard`,
  `orchestrator`, `optimize`, `game.breakout`, `ui.web`, `ui.browser`,
  `ui.tui_web`, `image_to_markdown`, `lint`, `llm_caret`, and `mcp`.
- `compiler_entrypoint/inventory_scratch.spl` + `compiler_inventory_checked_read_spec.spl`:
  resolved and converted together in **#11420** (left non-Option `event == nil` untouched).
- Remaining in `src/app`:
  - `itf` (`~25` `any`-typed sites, plus existing `c2fc6095f61` conversions): need typing first.
  - `file_read_bytes` / `rt_*` / `sys_get_args` / `env_get` / `input()` / `to_int()`
    results, pre-allocated slot tables (`bounded_channel.spl`), and unprovable
    `~600` untyped / sentinel sites (e.g., `assistant_import.spl`,
    `assistant_collectors_text_json.spl`, `claude_full/`, `active_buffer()`).
  - Audit of prior chained-call locals / `extern fn -> T?` / remaining `build`
    (`#11316`) left as follow-up if needed.

## Spec asserts — DONE for provable Options (#11420 + #11391)
- Deleted stray tracked file
  `test/01_unit/lib/common/text_layout/.spipe_cov_*_font_renderer_spec.spl` in **#11391**.
- Re-examined the 10 dropped `test/01_unit` specs + non-unit specs in **#11420**
  (**18 files, 139 conversions**, all 17 baseline verdicts preserved):
  - Converted 7 of the `test/01_unit` list: `enum_contract_hir_wiring_spec`,
    `reverse_reference_sort_equivalence_spec`, `hir_codec_nonfatal_existing_spec`,
    `compositor_content_registry_spec`, `host_compositor_entry_spec`,
    `usb_hid_input_backend_spec`, `ipc_spec`.
  - Intentionally left 3 untouched: `facet_hir_codec_compat_spec` (already deleted
    in `77f9303f22cc`), `async_ui_spec` (direct `rt_channel_try_recv` wrapper),
    `jit_typed_ir_equivalence_spec` (`compiler.backend.jit_typed_ir` absent on `release/1.0.0`).
  - Converted 4 orchestrator specs, `physical_vulkan_2d_qualification_spec`,
    `db_sdn_spec` (canonical `test/03_system/stdlib/database/`),
    `retained_private_credential_v2_spec`, `showcase_hosts_spec`,
    `library_mode_cache_io_spec`, and `compiler_inventory_checked_read_spec`.
  - Left untouched with exact reasons: `hosted_tcp_boundary_spec` (`sosix_tcp_*` wraps
    `rt_io_tcp_*`), `structured_owner_task_lifecycle_spec` (`structured_task_group`
    absent), `test/system/database/db_sdn_spec.spl` (legacy duplicate), `app/ui/ipc_spec` (0 `nil` asserts).
- Remaining:
  - `~485` non-provable `to_equal` nil asserts needing hand typing.
  - Owner decision: are the `~140` `to_be(true|false)` nil asserts in scope?

## Code generators and GPU library — DONE (#11391, #11411)
- Generators (**#11391**): `src/app/desugar/trait_desugar.spl`,
  `src/app/desugar/context_params.spl` (optional `T`), and
  `src/compiler/90.tools/sffi_gen/resource_wrapper_gen.spl` updated to emit
  `None` (with updated goldens); remaining generators swept with no other safe Option `nil` emissions.
- GPU library (**#11411**): **50 files, 197 sites** converted across
  `src/lib/gc_async_mut/gpu/` (`cuda/`, `rocm/`, `vulkan/`, `torch/` have 0
  non-comment `nil` sites); 12 non-Option/`env_get`/`to_i64`/`rt_*` handle sites left untouched.

## Bool flags → enums — DONE (#11399)
- **#11399**: converted `retire` and `pinned` flags in
  `src/lib/nogc_sync_mut/io/process_ops.spl` (`LaunchRetirementMode`,
  `ObservationPinMode`) + 7 external call sites across 3 files + re-exports.
- Surveyed `src/app/wm_compare_host/process_ops.spl` and `env_detect` copies
  (`nogc_sync_mut`, `nogc_async_mut`, `gc_sync_mut`, `gc_async_mut`): 0 behaviour-selecting bool flags present.

## Refactor auto-fix rules (opt-in) — DONE (#11394, #11409)
- Implemented `PRIV-PUB-001` (opt-in safe rule, fails closed unless whole-repo
  scan, hardened with `PrivPubScanMode` enum + `unit RepoFileCount: i64` in **#11409**)
  and `UNIT-WRAP-001` (opt-in suggestion-only `unit` proposal), wired into
  `src/app/io/cli_lint_commands.spl`, excluded from `registry.spl` defaults,
  and verified with `priv_pub_safe_fix_spec.spl` (20/20) and `unit_wrap_suggestion_spec.spl` (15/15).

## Remaining / Later
- Hand-type remaining non-provable untyped / `any`-typed sites (`src/app`, `src/compiler` preserved sites, `~485` `to_equal` spec asserts) and decide `~140` `to_be(true|false)` spec asserts.
- Revisit formal-verification-pinned files (`src/verification/cache_protocol/source_bindings.txt`) only alongside corresponding model updates.
- Escalate `NIL-UNSAFE-001` from warn to error once remaining unprovable/typed counts are near zero.
- Eliminate `Option`.
