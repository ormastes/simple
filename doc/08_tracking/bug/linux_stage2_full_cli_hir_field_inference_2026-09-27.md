# Linux Stage2 full CLI HIR field inference failure

Status: open, 2026-09-27. Isolated checkout:
`/home/ormastes/simple-collection-planner-shared`. The Stage2 candidate
passed frontend admission in both bootstrap modes and passed the positional
struct receiver/runtime route after the `starts_with`/`ends_with` text
representation fix. The phase verification matrix then failed at
`compiler_cli_build`.

## Evidence

The matrix invoked the admitted pure-Simple Stage2 compiler with
`native-build --source src/compiler --source src/app --source src/lib
--entry-closure --entry src/app/cli/_CliMain/main_and_help.spl`, using its
producer-bound cache. Its summary reports `compiler_cli_build=FAIL`, status 1,
elapsed 1006 seconds, max RSS 4,835,796 KiB; 2,327 files compiled and 30
failed in one shared HIR field-type-inference family. Test-runner build and
compiler/interpreter/loader suites were consequently blocked or unsupported.
No full CLI artifact or passing matrix was produced.

Representative errors include `src/compiler/10.frontend/core/interpreter/resolve.spl`
(`ANY.param_names`), `src/compiler/70.backend/backend/common/c_abi_type_mapping.spl`
(`ANY.id`), `src/compiler/99.loader/loader/module_loader.spl` (`ANY.ty`),
`src/app/ide/feature_report.spl` (`ANY.id`), and
`src/lib/nogc_async_mut/database/bug.spl` (`i64.severity`). The source of the
diagnostic is the Rust bootstrap HIR access lowerer at
`src/compiler_rust/compiler/src/hir/lower/expr/access.rs:447`; its dynamic
receiver fallbacks require unambiguous field layout evidence. The exact loss
of receiver type or declaration context in this full build is not yet proven.
Do not replace these errors with guessed field slot zero or a stub binary.

Logs and receipts:
`build/collection-planner-linux-bootstrap/stage2-compiler-tests/x86_64-unknown-linux-gnu/verification/{summary.env,logs/compiler_cli_build.log}`
and `build/collection-planner-linux-bootstrap/logs/x86_64-unknown-linux-gnu/stage2-compiler-tests.log`.
The admitted Stage2 compiler remains a compiler-only bootstrap artifact; it
does not supply a certified `test` command. The diagnostic work below narrowed
the failure to missing receiver and declaration evidence. The next action is
to trace where that evidence is lost in the HIR/module boundary, fix its owner
pipeline, and rerun the failed shard with its producer-bound cache before a
full matrix retry.

## Cache-preserving diagnostic

A single-file mini build of `resolve.spl` reproduced an `ANY.name` ambiguity,
but lacked the full CLI context and is not treated as the matrix failure.
Rerunning the exact failed full CLI task with
`SIMPLE_DEBUG_FIELD_FAIL=1` and the same producer-bound cache reused 2,324
objects, compiled 3, and again failed 30. The debug trace shows the actual
`ANY.param_names` failure with `candidates=[]` and `ambiguous=true`; many
other failed names have the same shape. `ANY.node_id` had a `LayoutBox`
candidate but no corresponding global definition. This confirms that a
single receiver-blind field-slot guess would be unsound. The unresolved work
is to retain the receiver's nominal type or import its declaration through
the full CLI's HIR/module boundary, then verify the failed shard and matrix.

## First failure's declared-type route

`resolve_function` in `src/compiler/10.frontend/core/interpreter/resolve.spl`
binds `val d_node = decl_get(decl_id)` and then reads `d_node.param_names`.
The sole `decl_get` declaration is in
`src/compiler/10.frontend/core/_Ast/module_state.spl` and explicitly returns
`CoreDecl`; `CoreDecl` is declared in `core/ast_types.spl`. This call has
source-level nominal return evidence, but the failing HIR receiver is `ANY`.
The native project scanner captures declared free-function return types in
`imports.rs`, `module_pass.rs::populate_global_fn_return_types` resolves them,
and `expr/mod.rs::named_callable_return_type` consults that map at calls.
The next focused diagnostic should check whether the full build retains the
`decl_get -> CoreDecl` row, resolves `CoreDecl` in this module, and carries the
resolved result through `stmt_lowering.rs` into `d_node`. This route is
source-backed; the exact failing link remains unverified. The other 29 errors
must be grouped by their own receiver provenance before changing the shared
lowerer.
