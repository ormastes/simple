# Phase 3 (LLVM) Build Warning Burn-Down Report (2026-11-25)

Baseline: [phase3_build_warnings_report_2026-11-25.md](phase3_build_warnings_report_2026-11-25.md) (`C:\dev\p3diag\p3fix2_ll\build.log`, `1,587` unique warnings / `39,896` total diagnostic lines across `24` MIR shard workers).

## Summary by Category

| Warning Category | Baseline Unique (`p3fix2_ll`) | Current Status on `release/1.0.0` | Landed / Open PRs |
|---|---:|---|---|
| `[hir-lower] WARNING` (bare unit variants) | 8 | **0** (fixed in Wave 1) | `#11475` (`work/fix-p3-hir-bare-variants-20261125`) |
| `W-ANY-COMPILE-001` (`join_point_attr_registry.spl`) | 1 | **0** (fixed in Wave 1) | `#11467` (`work/fix-p3-wany-textspan-20261125`) |
| `[mir-lower] WARNING` (`TextSpan` field collision) | 1 | **0** (fixed in Wave 1) | `#11467` (`work/fix-p3-wany-textspan-20261125`) |
| `E-MC-ANY-001` + `E-MC-ANY-002` (89 modules) | 539 | **`any_sites=0, escapes=0`** under `any_escape_census.spl` (fixed in Wave 2) | `#11491`, `#11493`, `#11494`, `#11495`, `#11505`, `#11508` |
| `E-MC-REP-001` (153 modules) | 1,038 | **Autofix + unblock PRs ready** (blocked on seed rebuild + project context; see bug doc) | `#11468`, `#11490`, Wave 3P (`work/fix-rust-seed-rep-boundary-attr-20261125`, `work/fix-rep-boundary-autofix-policy-20261125`) |
| `enum-contract pass` | 0 | **0** | Already clean |

## Wave 1 — Non-REP/ANY Warnings + EasyFix Infrastructure (Merged)

- **PR `#11475`** (`fix(compiler): eliminate 8 Phase-3 HIR bare unit variant warnings`): Typed match subjects and qualified enum arms in `driver_unit_tldr_imports_v1.spl` (`Option.None`/`Option.Some`), `weaving_config.spl` (`AdviceForm.*`), `inference_expr.spl` (`HirTypeKind.{Bool,Char}`), and `inference_expr_ops.spl` (`HirTypeKind.Str`).
- **PR `#11467`** (`fix(compiler,lib): ...`): Parameterized `_join_point_attr_promote_raw<T>(value: T)` in `src/compiler/10.frontend/join_point_attr_registry.spl` and renamed `db.accel`'s `TextSpan` to `AccelTextSpan` across `src/lib/nogc_sync_mut/db/accel.spl` and all 6 DB facades.
- **PR `#11468` & PR `#11490`**: Implemented `E-MC-REP-001` EasyFix rule (`lint_representation_boundary.spl`) and wired `simple fix --rule E-MC-REP-001` in `src/app/io/cli_lint_commands.spl`.
- **PR `#11472`**: Implemented and wired opt-in EasyFix rules `W-BARE-VARIANT-001`, `W-ANY-COMPILE-001`, and `W-MIR-STRUCT-COLLISION` in `src/compiler/90.tools/fix/rules/impl_/lint_warning_autofixes.spl` and `src/app/io/cli_lint_commands.spl`.

## Wave 2 — `E-MC-ANY-001` & `E-MC-ANY-002` Burn-Down (Merged)

All 89 modules (`539` unique diagnostics in `p3fix2_ll`) were verified at **`any_sites=0, escapes=0, unanalyzable=0`** via `src/app/check/any_escape_census.spl` across 6 parallel disjoint PRs (`62` source files modified):
- **PR `#11491`** (`lib.nogc_sync_mut`, 10 modules): `146` -> `0` (`deflate`, `lz77`, `inflate`, `url`, `test_runner_types`, `http_client_core`, `native_tool_authority_v1`, `linux_process_owner`, `windows_process_owner`, `log`).
- **PR `#11495`** (`lib.common`, 6 modules): `111` on HEAD (`153` in `build.log`) -> `0` (`serialization/__init__`, `format_utils`, `sha256`, `binary_io`, plus `text_advanced` & `xxh3` verified clean).
- **PR `#11493`** (`compiler.frontend/hir/types/semantics/common`, 21 modules): `8` on HEAD (`61` in `build.log`) -> `0` across 8 modified + 13 pre-cleaned files.
- **PR `#11505`** (`compiler.driver`, 16 modules): `13` on HEAD (`56` in `build.log`) -> `0` across 11 modified + 5 pre-cleaned files.
- **PR `#11508`** (`compiler.backend/mir/loader`, 27 modules): `81` in `build.log` -> `0` across 21 modified + 6 pre-cleaned files.
- **PR `#11494`** (`app`/`scv`/`nogc_async_mut`, 8 modules): `49` -> `0` (`native_build_producer_binding`, `structural_store_v1`, `action_identity`, `artifact_receipt`, `bug`, `validation`, `worker_hir_profile_v1`, `sprof_collection_profile`).

## Wave 3P — `E-MC-REP-001` Unblock Checklist

Tracked in `doc/08_tracking/bug/rep_boundary_p3_seed_and_project_context_blockers_2026-11-25.md`:
1. **Done** — Rust seed `@representation_boundary` attribute/directive support merged (`#11521`); seed rebuilt from merged source and verified on an annotated probe (old seeds still reject the attribute until promoted).
2. **Done** — Policy-compliant `E-MC-REP-001` EasyFix reading `config/policy/unsafe_region_owners.sdn` merged (`#11518`); `impl`/`extend` methods and unmatched paths fail closed to `FixConfidence.Uncertain` suggestions.
3. **Done (wiring)** — `CompileOptions.representation_project_root` + nearest-`simple.sdn` per-source context derivation wired into `aot_native_project_with_backend` and `bootstrap_native_driver_with_backend_fixed_v1` (`#11532`, spec `representation_project_context_derivation_spec.spl` 13/13). Still open: HIR body-cache metadata transport (perf) and Opus `review_ref` promotion in `config/policy/unsafe_region_owners.sdn`.
4. In progress — Run `simple fix --rule E-MC-REP-001 --safe-only` across the 153 modules (with per-fix review) and re-run a full Phase 3 LLVM build to confirm 0 warnings.
