# Lane: 1.0.0 beta release (ex-codex 019fb160)
Goal: next 1.0.0 beta (beta2 if version unchanged): local release process, fix memory/perf bugs, full bootstrap for all platforms (except mac), GH Actions release must actually succeed.
Status: stage2 parser blocker removed, stage3 name-resolution/IR gate still hard-blocked.

Latest fresh rebuild: `scripts/bootstrap/bootstrap-from-scratch.sh --mode=dynload --output=build/bootstrap/release_beta_verify --no-mcp --jobs=min`
- Stage 2: PASS (`build/bootstrap/release_beta_verify/logs/x86_64-unknown-linux-gnu/stage2-native-build.log` ends with `Build complete: 728 compiled, 0 cached, 0 failed`; binary at `build/bootstrap/release_beta_verify/stage2/x86_64-unknown-linux-gnu/simple`).
- Stage 3: FAIL (`stage3` strictly fails with strict bootstrap gate), first errors are unresolved type/name errors in `src/compiler/types/type_infer/inference_effects.spl` (`Effect`, `Span`, `DimExpr`, etc.) and compiler/runtime modules (`MirFieldDef`, `SymbolId`, `rt_file_rename`, ...).
- Repro of old stage2 parser fail is no longer present after source fix: cached pre-fix stage2 failed on `true_target.id`, while fresh stage2 now compiles `/tmp/repro_beta.spl`.

See:
- `doc/08_tracking/bug/parser_true_false_prefix_call_arg_2026-08-01.md`
- `src/compiler/10.frontend/core/parser_expr.spl` (`parse_call_arg_raw` now guards true/false prefixed call arg identifiers)
- `doc/03_plan/sys_test/release_workflow_checkers.md`
Next: clear the stage3 `in-process native-build` unresolved-type gate, then run release checkers and GH release workflow.
