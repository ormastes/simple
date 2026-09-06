# BUG: flat bootstrap AST bridge — invalid `bitcast i64 to i1` on bool tail-merge + text value corruption

**Status:** RESOLVED (runtime-verified 2026-07-17)

## Trigger

`flat_is_bootstrap_entry_path(path)` at
`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl:50` routes the
ENTIRE entry file through the minimal flat bootstrap bridge
(`lower_bootstrap_flat_function`/`lower_bootstrap_flat_expr` in
`src/compiler/20.hir/hir_lowering/_Items/{declaration_lowering,module_lowering}.spl`)
whenever the entry is `bootstrap_main.spl` — matched via
`SIMPLE_NATIVE_BUILD_ENTRY` (set unconditionally by
`src/app/io/_CliCompile/compile_targets.spl:770`), INDEPENDENT of the
`SIMPLE_BOOTSTRAP` env var. All HIR is `HirTypeKind.Infer` and every call is
`MethodResolution.Unresolved`.

## Defect 1: invalid LLVM opcode

A `bool`-returning function whose value comes from an if/elif/else tail-merge
emits `bitcast i64 to i1` (must be `trunc`). `llc` rejects the module.
Reproducible on any bool tail-merge under the bridge.

## Defect 2: text value corruption

A `text`-returning function or array-index value routed through the bridge
silently corrupts: prints a raw pointer as digits, `.len()` returns 0.
Confirmed even for a direct `args[2]` access (no helper involved).

## Fix direction

Preferred: narrow the filename gate to `SIMPLE_BOOTSTRAP == "1"` only (in
progress under #138) so the normal path uses the full typed pipeline; the
bridge then only serves seed-stage2, whose 6-function bootstrap_main avoids
these shapes. If the bridge must keep serving richer code, fix the bool
tail-merge to `trunc` in `50.mir`/`70.backend` and root-cause the text
representation loss.

## Runtime verification (2026-07-17)

Source read of `module_assembly.spl:109`: `flat_ast_to_module` only returns `flat_empty_module` when `flat_bootstrap_enabled() and not flat_is_bootstrap_entry_path(path)` — gated behind `SIMPLE_BOOTSTRAP=="1"` (preferred fix landed). Native-built with `SIMPLE_BOOTSTRAP` unset: both bool if/elif/else and text Option unwrap ran correctly without bitcast crash or corruption. Residual scope (actual `SIMPLE_BOOTSTRAP=1` stage2 self-compile) untested under hard rules.
