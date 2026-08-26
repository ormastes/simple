# Stale-snapshot clobber `4edef8fab8e` ("feat: snapshot current development state")

**Date found:** 2026-08-26 (commit landed 2026-08-26 01:21 UTC)
**Scope:** 624 files, +23,614 / -45,183 lines. Whole-working-copy snapshot of a
stale tree (see `.claude/rules/vcs.md` § "Sync must never clobber").

## Evidence it is a partial, stale snapshot (not a deliberate change)

- `src/compiler/20.hir/hir_lowering/module_surface_types.spl` lost the
  `semantic_hash0..5` fields added by `7f79377f996` (-111 lines), while
  `module_surface_declarations.spl:349` and
  `module_surface_source_identity.spl:167` at the same commit still construct
  and read them -> `class ModuleSurface has no field named semantic_hash0`.
- `src/lib/common/crypto/sha256.spl` lost `Sha256StreamV1` /
  `sha256_stream_v1_*` (-174 lines) while
  `src/compiler/20.hir/hir_lowering/module_surface_semantic_projection.spl:9`
  and `src/compiler/10.frontend/generated/ast_semantic_value.spl:8` still
  import them -> `function sha256_stream_v1_new not found` on every spec that
  lowers HIR.
- `test/01_unit/compiler/frontend/lexer_types_spec.spl` was truncated to a
  1-line stub (its mirror `test/unit/...` is also a stub).

## Repaired so far (restored from `4edef8fab8e~1`, no forward commits on those paths)

- `src/lib/common/crypto/sha256.spl`
- `src/compiler/20.hir/hir_lowering/module_surface_types.spl`
- `test/01_unit/compiler/frontend/lexer_types_spec.spl`

## Still clobbered (largest src deltas, NOT restored here)

`src/runtime/runtime_native.c` (-2125), `src/compiler/20.hir/generated/hir_codec.spl`,
`src/os/installer/image_builder.spl`, `src/os/apps/servers_user/http1_request_frame_owner.spl` (deleted),
`src/lib/nogc_async_mut/fs_driver/mount_table.spl`, `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`,
`src/compiler/20.hir/hir_lowering/_Expressions/expression_support.spl`,
`src/compiler/80.driver/driver_hir_pipeline_lowering.spl`,
`src/compiler/35.semantics/lint/cow_alias_hotpath.spl` (deleted), and ~600 more.
Full list: `git show 4edef8fab8e --stat=200 -- src`.

## Unblock condition

Per-file audit of `git show 4edef8fab8e -- <path>`: restore from
`4edef8fab8e~1` every path where HEAD references a symbol the clobbered file no
longer defines and no forward commit touched the path since.

## Update 2026-08-26 (second pass)

Additional restores landed: `00.common/assurance/warning_phase.spl` (+ spec,
guide, review report — all four deleted by the clobber) and
`80.driver/driver_safety_severity.spl`; `assurance_warning_phase_spec` is 18/18
green again.

**Lint engine is entangled — do NOT restore it file-by-file.** Restoring
`90.tools/lint/_LintMain/{config_and_model,lint_checks,nonexistent_type_lints}.spl`
and `35.semantics/lint/cow_alias_hotpath.spl` fixes the 4 red examples in
`test/01_unit/compiler/lint/raw_rt_access_spec.spl` (missing
`lint_source_for_parsed_append` / `last_resolved_path` /
`check_cow_alias_hotpath_snapshot` / `raw_rt_wrapper_binding_is_unshadowed`)
but regresses `riscv_rtl_debuggability_spec` 11/14 -> 1/14 with
`method sort_by not found on type array` from the pre-clobber lint pipeline.
The lint subsystem needs an all-or-nothing restore audited together.

Separate finding (may predate the clobber):
`src/compiler_rust/lib/std/src/bare/hal/uart.spl:79-80` calls
`Option.some/none` but `core/option.spl` declares `Some/None`;
`hal_traits_spec` fails on it, and editing that file (either worktree) does not
change the outcome, so the interpreter resolves `std.bare.hal.uart` from a
third location — see memory note "binary reads stdlib from build worktree".
