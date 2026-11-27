# External imported return diagnostic reproduction

Source: `test/02_integration/compiler/hir/inferred_return_diagnostic_cli_spec.spl`.
Authored manual; docgen and all four examples NOT_RUN.

Requires an admitted absolute `SIMPLE_BIN`, repository working directory, and
coordinator-owned outer process-tree watchdog (600 seconds for four bounded
120-second children plus setup). No Rust-seed fallback or blanket skip.

Each case writes real model/provider/consumer source to its own directory under
`build/test-artifacts/inferred-return-cli/`, with a freshly cleared isolated
cache/output. `src` has no written annotation. The external CLI receives direct
argv: `native-build --source <case>/src --entry <case>/src/app/main.spl
--entry-closure --threads 1 --cache-dir <case>/cache -o <case>/program`, with
`SIMPLE_BOOTSTRAP=1`, `SIMPLE_TYPECHECK_WARN=1`,
`SIMPLE_TYPECHECK_PROFILE=robust`, and `SIMPLE_FRONTEND_DIAG=1`.

The worker routes through `cli_native_build_with_environment_variant_policy_v1`
and `native_build_compile_with_collection_profile` to the full driver. The
HIR lowering phase runs its typecheck warning pass and prints the frontend
finding. This differs from the single-file `simple check` route, which does
not construct the frozen imported surfaces required by this regression.

| Case | Required result |
|---|---|
| Provider omitted return | Exactly one missing-signature reason, frontend code, binding, declaration line 4 and function identity |
| Re-exporting facade omitted return | Same exact warning requirements |
| Provider explicit Node return | Successful native compilation, no W-HIR-INFER-001 |
| Facade explicit Node return | Successful native compilation, no W-HIR-INFER-001 |

Omitted-return cases accept completed exit 0 or 1 because they qualify warning
emission, not downstream compilation or successful imported return inference.
Timeout/crash/launch failure statuses fail. Output is capped at 4 MiB and saved
with the actual exit status in each case directory. Setup has a 5-second/64-KiB
bound. The test does not execute produced programs or claim child timeout alone
proves descendant retirement. Before the diagnostic repair, the missing
warning makes the ordinary omitted-return cases fail.

AST annotation provenance is exercised through unannotated source; exact receipt
and independent retained-metadata assertions remain in the companion unit spec.
Runtime and mutation execution remain NOT_RUN.
