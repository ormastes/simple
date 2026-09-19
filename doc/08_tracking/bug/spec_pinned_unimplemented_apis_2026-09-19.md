# Never-implemented APIs pinned by specs (2026-09-19 lib sweep)

Date: 2026-09-19
Lane: suite-2026-09-18

These specs pin APIs with ZERO definitions anywhere in src/ (verified by
grep across mainlane and the parent clone). They arrived via merge
e274cd33719 (or earlier carry merges) without their implementations. Each
needs a feature-implementation lane or a spec-retirement decision; fixing
at the spec level would require inventing behavior.

| Spec | Missing API |
|---|---|
| test/01_unit/lib/aspect_pack_lifecycle_spec.spl | apk_activation_{claim,advance,publish,fail,state,diagnostic}_v1, ApkActivationClaimV1, APK_AS_* states, apk_load_facet_owned_v1 (REQ-APK-P05/P06b late-lifecycle state machine) |
| test/01_unit/app/cli/lsp_query_worker_protocol_spec.spl | app.cli lsp_query_worker + LspQueryWorker* protocol surface (carry commit f14f4dba5b9) |
| test/01_unit/lib/std/parser/error_recovery_spec.spl | ContextualSyntaxError / ErrorBuilder / Span DSL (791-line spec-first draft) |
| test/01_unit/lib/std/json_spec.spl | JsonValue OO layer |
| test/01_unit/lib/std/collection_helpers_spec.spl | ~40 helper functions |
| test/01_unit/lib/std/game_engine/effects_spec.spl, ml/tracking_spec.spl, core/dsl_spec.spl | feature modules never landed |
| test/01_unit/lib/common/math/field/fe_p256_spec.spl | fe_p256 module (spec is its own reproducer) |
| test/01_unit/lib/common/context_sharing_spec.spl | context_def/get_let protocol |
| test/01_unit/lib/enterprise_*_spec.spl (nogc_sync_mut) | std.nogc_sync_mut.enterprise_{assets,expense,quality,warehouse} modules |
| src/app/cache_gateway/* | compiler.driver.cache.remote.namespace_policy (HEAD does not compile) |

## Seed defects blocking otherwise-valid specs (verified by probes)

- Class instances deep-copy on assignment/argument/field access: specs
  pinning shared-reference design need registry/handle indirection
  (GcHandle, parent_commit, async Promise/Future resolved this way).
- If-expression with an `as` cast in one branch evaluates the false branch
  to nil; statement form required.
- Nested-lambda writes to captured locals are silently dropped.
- Iterable impl on List rejected by the seed checker.
- Some externs registered in source (rt_browser_renderer_spawn_sandboxed,
  rt_channel_free, rt_file_copy_create_excl_no_follow,
  rt_file_read_regular_no_follow_last_failure) are absent from the deployed
  seed binary.
- process_run/process_run_bounded execute the child twice (see
  posix_spawn_and_seed_process_debt_2026-09-19.md).
