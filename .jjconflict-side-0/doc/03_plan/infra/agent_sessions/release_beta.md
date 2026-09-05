# Lane: 1.0.0 beta release (ex-codex 019fb160)
Goal: next 1.0.0 beta (beta2 if version unchanged): local release process, fix memory/perf bugs, full bootstrap for all platforms (except mac), GH Actions release must actually succeed.
Status: stage2 parser blocker removed, stage3 name-resolution/IR gate still hard-blocked.

Goal: produce the next 1.0.0 beta from an immutable admitted candidate, with
reviewed exact bug-fix convergence, full required bootstrap/whole-test evidence,
signed promotion, and byte-identical package publication.

See:
- `doc/08_tracking/bug/parser_true_false_prefix_call_arg_2026-08-01.md`
- `src/compiler/10.frontend/core/parser_expr.spl` (`parse_call_arg_raw` now guards true/false prefixed call arg identifiers)
- `doc/03_plan/sys_test/release_workflow_checkers.md`
Next: clear the stage3 `in-process native-build` unresolved-type gate, then run release checkers and GH release workflow.
