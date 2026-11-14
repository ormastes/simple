# HIR lambda parameter hint outlives its module scope (E-HIR-VISIT-UNHANDLED, run 29)

- Status: fixed in source (`work/cli-build-hir-exit-20261114`); takes effect
  when the next Stage 2 is built from it. The admitted run-29 Stage 2 is frozen
  and keeps the defect.
- Found: bootstrap-fable run 29, Phase 2 matrix, `compiler_cli_build`
  (`result=FAIL status=1 elapsed_seconds=4279 max_rss_kib=21746236`).

## What ended the process

Not a timeout (task 14400 s, native-internal 7200 s, scale 4), not the RSS
guard (`compiler_cli_build.max-rss-kib` = `Command exited with non-zero status 1`),
not OOM. The HIR worker called `hir_walk_unhandled`
(`src/compiler/20.hir/generated/hir_visitor.spl:23-26`: `print` then `exit(1)`)
while lowering module 2758/3145, `compiler.driver.watcher.watcher_client`.
The message is in the log. Its last bytes (`od -c`) are
`...unhandled at walk_hir_type\n`. It looks missing because it sits at the end
of a 63 KB line. The frozen Stage 2 binary drops the trailing newline of every
`eprint` imported from `process_ops`, so all 270 `[hir-reexport-chase-unresolved]`
warnings and the `[hir-cache-store] refused reason=codec detail=unencodable
HirTypeKind enum` line before it run together into that one line.

## Root cause

`HirLowering.lambda_param_hint` (types.spl) is staged for each method-call
argument (`stage_lambda_param_hint`) and consumed by the next lambda. It was
not reset in `begin_module` and is not a promoted phase memo. A shard worker
lowers many modules with one lowerer. Each module's HIR lives in a transient
scope that is reclaimed after the module. So after the first module the field
held a `HirType` inside reclaimed memory.

In `watcher_client.spl`, the first lambda (`fn(p: text) -> i64: 0`) is an
argument to a plain call, so nothing restages the hint in that module. The
`fn(...)` lambda parser discards the parameter annotation
(`_ParserPrimary/primary_expr.spl` parses the type and drops it). So the
parameter counted as unannotated and took the stale hint as its type, which
was garbage. Both exhaustive matches then failed: the codec store and
`walk_hir_type`.

The two generic-owner prescan maps, `struct_type_param_names_by_name` and
`class_method_return_types_by_name`, have the same lifetime defect. Their
sibling `struct_field_types_by_name` was already reset.

## Reproduction (admitted Stage 2, ~2 s of HIR)

Three modules placed under `src/app/zz_repro_hir/` (fixtures kept untracked at `build/repro/zz_repro_hir/` in the worktree),
`native-build --threads 1 --entry-closure`:

- `ha.spl` ends with a method call that takes an argument (`names.join(",")`).
- `hb.spl` has `hb_apply(a, fn(p: text) -> i64: 0)` before any method call.
- Result: `E-HIR-VISIT-UNHANDLED: HirTypeKind variant <unknown> unhandled at
  walk_hir_type`, plus a codec refusal on `hb.spl`.
- Control: put `val t = a.replace("x", "y")` in `hb.spl` before the lambda.
  The build passes and the binary prints `14`.
- Lowering `watcher_client` as module 2 of a fresh worker passes.

## Fix

`begin_module` now resets `lambda_param_hint`,
`struct_type_param_names_by_name` and `class_method_return_types_by_name`.
Spec: `test/01_unit/compiler/hir/hir_lowering/begin_module_detaches_module_owners_spec.spl`.
At the spec commit the seed reports 5 passed and 2 failed: the hint
scenario and the map scenario. After the fix all 7 pass.

`class_method_return_types_by_name` is only written for the current module's own
generic impls. So a module lowered in a fresh process never had an entry for an
imported owner. The reset turns an order-dependent, dangling lookup into a
consistent miss, which is the documented fallback that leaves the call untyped.
It is not a regression.

## Not fixed here (follow-ups)

- `fn(p: T) -> R:` lambdas lose their parameter and return annotations in the parser.
- The frozen Stage 2 binary loses the newline of imported `eprint`, which is
  why the error line was hard to find. Stage 2 compiles an imported `eprint`
  correctly in a 68-module closure (the probe printed `AAA\nBBB\n`). There are
  two open candidates: a parent-generation (Stage 1) codegen defect, or
  codegen that depends on closure size and would also affect Stage 3. Check the
  next Stage 3 logs for joined `eprint` lines.
- `accessor_warned_keys` and `impl_textual_method_keys` also survive
  `begin_module` and hold text allocated in a module scope.
- A repro build of a 1465-module closure crashed its MIR shard worker with
  SIGSEGV before claiming any module. The log is `build/repro/w2b.log` in the
  worktree.
- `native-build` without `--threads 1` failed with `closure identity differs`
  between the two HIR workers when the entry was outside the tracked tree.
