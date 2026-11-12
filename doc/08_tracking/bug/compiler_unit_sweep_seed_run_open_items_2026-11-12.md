# Compiler unit sweep (seed-run) 2026-11-12: open items that need an owner

**Status:** open. **Found by:** the compiler unit-spec sweep on `release/1.0.0` at
`c2c31adeb06`. **Evidence class:** seed-run only. The runs used the Rust seed's
`test` command (`pinned-bfe789dd4118`); no pure-Simple full CLI is deployed on
this host yet. Re-check every item once one exists.

The stale source-pin specs were retargeted in a separate PR. The items below
were deliberately **not** "fixed" in a spec. In each case the spec pins an
invariant that current source contradicts, or the failure is outside the
code/spec, so a retarget would be weakening the assertion.

## Owner decisions (spec invariant vs current source)

| spec | failure | finding |
|---|---|---|
| `bootstrap/stage4_streaming_surfaces_contract_spec.spl` | `expected 20854 to be less than 20000` | `src/compiler/70.backend/backend/interpreter_binop.spl` grew past its 20000-byte budget. The budget was not raised; either split the file or raise the budget by owner decision. |
| `bootstrap/stage4_unlimited_streaming_ownership_spec.spl` | `low_memory` present in the streaming selector | a528caf4937 added `driver_low_memory_streaming_requested_values(ctx.options.low_memory, ...)` as an extra OR route in `driver_streaming_surface_route` (`src/compiler/80.driver/driver_phase_gates.spl:87`). The spec requires selection to be independent of low-memory policy. |
| `bootstrap/stage4_fix_tool_sync_entry_spec.spl` | file `src/compiler/tools/fix/main.spl` missing | The only fix CLI on the tree is `src/compiler/90.tools/fix/main.spl`, and it is `async fn main() -> Int` with `dry_run: Bool` and `.slice(`. That is exactly the shape the spec forbids, so retargeting the path would leave the spec red. |
| `bootstrap/specialized_template_context_contract_spec.spl` | both pinned files missing | ab9305d783e (40.mono removal) deleted `linker/linker_context.spl`, `pipeline/compiler_context.spl` and the specialization hooks. The spec pins a removed feature; deleting it needs owner approval. |
| `bootstrap/stage2_capability_stage4_guard_spec.spl` | `SIMPLE_BOOTSTRAP_STAGE4=0`, "Stage 4 remains bound to verified Stage 3" missing | `scripts/bootstrap/bootstrap-from-scratch.sh:6247-6290` still prints `using seed for stage 4` on a failed Stage 2 capability probe. Owned by the bootstrap-script lane; not touched here. |
| `bootstrap/hir_statement_shared_binding_contract_spec.spl` | `var rt_hir: HirExpr? = nil` + reassignment | 064d40e5896 introduced this shape at `src/compiler/20.hir/hir_lowering/statements.spl:1077`. It is a native-lane workaround (`match rt_val: case Some` never matched), and the spec forbids it. Decide between the spec and the workaround. |
| `bootstrap/stage4_streaming_surfaces_contract_spec.spl` (2 of 4 tests) | `SIMPLE_STAGE3_STREAMING_SURFACES=1` missing | a1d66e52206 flipped Stage 3 streaming to `=0` at `scripts/bootstrap/bootstrap-from-scratch.sh:4738,:5876`, and the worker scripts also set `=0` (`stage3-native-build-worker.sh:163`, `resume-stage3-from-admitted.sh:995`). The commit message gives no reason. Retargeting would flip the invariant. |
| `bootstrap/newunit_pool_reset_contract_spec.spl` (3 tests) | `newunit_project_*`, `builder_owner.add_surface(`, `parse_all_legacy_impl` missing | These symbols exist nowhere in `src/`, and `git log -S` finds no commit that ever added them. The spec arrived in the mass merge e274cd33719, describing an API that never landed (`units_newunit_registry_spec.spl:29-33` imports them too). Implement the API or delete the spec. |
| `bootstrap/stage4_cli_ops_stderr_facade_spec.spl` | `stderr_write` facade missing | `src/app/io/cli_ops.spl:127-128` is still `fn _cli_eprint(msg: text): eprint(msg)`; the canonical-stderr routing was never implemented. |

## Environment (d)

| spec | failure | finding |
|---|---|---|
| `bootstrap/llvm_aggregate_shared_binding_contract_spec.spl` (2 tests) | `expected -1 to equal 0` | It spawns `bin/simple compile`, and a fresh worktree has no `bin/simple` (exit -1). Needs a deployed full CLI. |

## Not yet triaged (behavioural; need a focused run)

- `bootstrap/entry_package_facade_precedence_spec.spl` (2 tests): `_driver_entry_import_module_paths(file_read(facade))` returns `[]` for a fixture `__init__.spl` holding `export use std.env.variables.{env_get_or}`. A standalone repro of the same scan on the same content (relative path, no `SIMPLE_SCV_SNAPSHOT_ROOT`) returns 1 path. The difference is in the fixture path or the snapshot-root env, not in the scanner.
- `20.hir/bootstrap_regressions/unresolved_name_eager_resolution_spec.spl` (2), `20.hir/export_origin_generated_comment_foreign_package_spec.spl` (1, new `W-HIR-UNDECL-IMPORT-001` on a package sibling that prebinds facade exports).
- `30.types/cfg_decl_check_spec.spl` (1): `semantic: private fn empty_type_env of type_infer_types.spl is not visible to type_infer/__init__.spl`. `src/compiler/30.types/__init__.spl:20` export-uses the private `empty_type_env` (and `empty_subst_map`).
- `30.types/written_any_compile_mode_spec.spl` (1).

## Side finding

`src/app/io/_CliCompile/native_build.spl:197` `_nb_resolve_segs` keeps its own
10-entry tier list in a non-canonical order (`nogc_async_immut` before
`nogc_sync_mut`). No `.spl` file imports that module. Either delete it or make
it use `source_root_std_family_order_v1()`.
