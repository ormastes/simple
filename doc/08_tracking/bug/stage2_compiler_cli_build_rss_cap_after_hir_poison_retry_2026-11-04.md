# Stage 2 `compiler_cli_build` rss-cap-exceeded: HIR poison then in-process retry (2026-11-04)

Status: **fix-implemented-verification-pending** (needs a sanctioned bootstrap rerun, s2d).

## Evidence (s2c, `/private/tmp/boot2-out/s2c`, macOS M4 24 GiB)
`stage2-compiler-tests/aarch64-apple-darwin/verification/logs/compiler_cli_build.log`:

1. Lines 13-43013: HIR pass #1 lowered **all 3020** modules in-process and stayed
   under the 12 GiB tree cap, then `[collect-all] 4 module(s) poisoned` ->
   `phase 3 FAILED`. Deterministic compile errors, not memory.
2. Line 43045: `[mir-shard] ... falling back to in-process unsharded MIR` -> the
   driver restarted load/parse/HIR **in the same process**.
3. Pass #2 hit `peak_rss_kib=13348288` at HIR 1665/3020 -> `rss-cap-exceeded`.

So the RSS kill is a consequence; the root cause is the poison.

## Root causes fixed
- `src/app/traceability/snapshot/git_provider.spl:158,172` used
  `"...^{commit}"`; `{commit}` is interpolation -> `unresolved name: commit`.
  Escaped as `^\{commit\}` (same idiom as `submodule_git_adapter.spl`).
  Verified with the s2c Stage 2 `compile`: 7 -> 0 `unresolved name: commit`.
- `materialize_imported_owner_parameter_dependencies`
  (`module_reexport_materialization.spl`) reported an imported owner's
  `where K: Eq + Ord` as `unresolved imported owner type parameter dependency`.
  `Eq`/`Ord` have no library declaration; local where-bound lowering
  (`types.spl` builtin bound arm) already treats
  Clone/Copy/Debug/Default/Drop/Eq/Ord as ambient. The check now does the same
  (only when the name still resolves nowhere). Poisoned `adaptive_map`,
  `adaptive_set`, `sprof_collection_profile`. Compiler change: verified only by
  the next Stage 2 rebuild.

## Follow-up fixes (work/bug-mirsig-20261104)
- **`expr?.method(args)` MIR failure** (`indirect callable lacks a proven
  function signature`, 6 sites in `git_provider.spl`, repro'd with the s2c
  Stage 2 `compile`): root cause is the self-hosted parser
  (`src/compiler/10.frontend/core/parser_expr.spl`, both postfix loops). Token
  `?.` was consumed as a plain field access -- the `?` was dropped and the
  following `(` built `Call(Field(base, m))`, an indirect call of a "field"
  on a `Result`. Now `base?.m(args)` parses as `MethodCall(Try(base), m, args)`
  -- the try-then-call meaning every in-tree `)?.m(` site relies on
  (git_provider, scv/db, compiler 50.mir/70.backend/80.driver). The field form
  `base?.f` is unchanged. Note: the Rust seed's *interpreter* gives
  `?.m()` safe-navigation semantics (wraps `Some`); the seed has no static
  lowering for it. Spec: `test/01_unit/compiler/frontend/optional_member_call_parser_spec.spl`
  (3/3; 2 of 3 fail without the parser change).
- **SUPERSEDED (work/bug-optchain-20261105): `?.` semantics reconciled.**
  The try-then-call parse above contradicted the language docs
  (`syntax_quick_reference.md` "Safe Navigation (`?.`)", incl.
  `result?.process()?.validate()`) and the seed (`OptionalMethodCall`:
  unwrap Some/Ok, else None; result wrapped in `Some`), and silently changed
  the meaning of documented optional-chaining sites (`linker_gen/parser.spl`
  x26 `dict["k"]?.as_text() ?? ""`, `svim/tui_shell.spl:124`). Decision:
  `?.` is safe navigation on BOTH compilers; try-then-access is spelled
  `(expr?).m()` / `(expr?).f`. The self-hosted parser now emits
  `OptionalChain` for `x?.f` and `Call(OptionalChain(x, m), args)` for
  `x?.m(args)` (previously it dropped the `?` for BOTH forms). Native MIR
  still has no OptionalChain lowering and rejects it LOUDLY
  (`E-MIR-EXPR-OptionalChain`) -- remaining gap. All 87 in-tree
  try-then-access sites (`)?.m(` / `)?.f` on Result-returning calls in
  git_provider, scv/db, task_runner journal, compiler 50/70/80, os, lib)
  were rewritten to the explicit `(expr?).x` form; on the seed they had been
  swallowing `Err` into `None`. Nil-guarded compiler sites
  (`record != nil and record?.f`) use `record.unwrap().f`;
  `70.backend/interrupt.spl` uses `if val`. Spec:
  `optional_member_call_parser_spec.spl` 5/5 on the seed (parser via the
  self-hosted frontend + runtime cases for both forms).
- `git_provider.spl:161,174` `"...^{tree}"` interpolated the local `tree`
  (still `""`) -> `rev^`; escaped as `^\{tree\}` (genuine source bug).
- **No in-process MIR retry after HIR compile errors.** A MIR shard child
  whose frontend stops on HIR diagnostics now writes `HIR_COMPILE_ERRORS`
  beside the MIR ledger (`native_mir_shard_record_hir_compile_errors_v1`,
  called after both collect-all summaries in
  `driver_hir_pipeline_lowering.spl`). The coordinator
  (`run_mir_shards`, and the focused-capsule path) maps the otherwise
  indistinguishable "fallback" (no claims) to "fail"
  (`native_mir_shard_outcome_after_hir_errors_v1`), so the build fails fast
  with the HIR errors already on stderr. Without the marker (transient/infra:
  no HIR inventory/cache) the fallback is kept. Spec:
  `test/01_unit/compiler/driver/native_mir_shard_spec.spl` (12/12).
- Verified in s2e (`/private/tmp/boot2-out/s2e`, PR #6708): Stage 2 sanity
  PASSED; `git_provider` no longer poisoned; on the remaining HIR errors the
  coordinator logged `HIR compile errors recorded by the shard frontend
  (errors=396 poisoned_modules=3); deterministic, no in-process MIR retry` ->
  `outcome=fail`, no second frontend pass, no rss-cap kill.
- s2e blocker: 3 modules (`sprof_collection_profile`, `adaptive_map`,
  `adaptive_set`) poisoned with `unresolved type: Eq` (71x). #6682 only
  silenced the dependency check; the imported owner's type-parameter bounds
  were still lowered as types in
  `project_imported_owner_type_parameters` (`module_callable_types.spl`),
  which lacked the builtin-bound erasure the local `lower_type_param` has.
  Now erased when the bound is a bare Clone/Copy/Debug/Default/Drop/Eq/Ord the
  owner does not declare (`hir_imported_bound_erases_builtin_v1`). Spec:
  `test/01_unit/compiler/20.hir/builtin_trait_where_bound_spec.spl` (6/6).
  Verification pending s2f.

## Remaining (not fixed here)
- `SHARD_TREE_HEADROOM_KB_V1` (24 GiB default) >= host RAM on a 24 GiB Mac, so
  the HIR worker pool is always 0 (`effective 0 kB`) and HIR runs in the
  coordinator. Not touched (reserve policy is owner-controlled); same for the
  12 GiB build memory reserve.
- HIR cache store `refused=363 reason=decode ... enum allocation failed`:
  separate codec defect, not causal.
- Single-module `compile` of `git_provider.spl` additionally reports
  `enum runtime ID collision: TextIoError` (process_ops) and unresolved
  `to_array`/`get` (sha1) then SIGSEGV; these did not appear in the s2c
  full-CLI log and look single-module-mode specific.
