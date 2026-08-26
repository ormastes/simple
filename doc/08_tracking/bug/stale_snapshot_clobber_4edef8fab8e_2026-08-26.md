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
