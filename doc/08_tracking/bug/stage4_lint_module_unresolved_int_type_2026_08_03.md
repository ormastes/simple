# Stage 4 lint-module unresolved `int` type

Status: focused repair verified; full x86 rerun pending
Severity: P1 bootstrap blocker
Owner: pure-Simple EasyFix module-boundary lint rule
Fix owner: `codex/stage4-x86-phase4` in `/home/ormastes/dev/pub/simple-stage4-x86-phase4`
Claimed source revision: `4c03aca49e6`

## Exact failure

The first full-resource x86 Stage 4 cycle after the backend-facade repair
crossed the former `BackendKind`/`CompiledSymbolKind` collision, completed HIR
for `compiler.backend.backend.compiler`, and reached HIR progress 448. It then
failed while lowering `compiler.tools.fix.rules.impl_.lint_module`:

```text
error: focused native-build: HIR lowering error in compiler.tools.fix.rules.impl_.lint_module: unresolved type: int
```

The cycle exited 1 after 41m52.57s at 24,343,824 KiB max RSS. No Stage 4
candidate exists, so the essential-tools smoke and all post-x86 platform rows
remain gated.

## Owner boundary

`src/compiler/90.tools/fix/rules/impl_/lint_module.spl` annotates
`_brace_delta` with the non-canonical named type `int`. The active HIR lowering
path recognizes the fixed-width primitive `i64`, while the legacy core-only
lowering's `int` compatibility spelling does not apply to this Stage 4 route.

The repair must remain local to the lint rule: use the canonical `i64` return
type, retain the inferred integer arithmetic, and do not broaden the resolver,
add a type alias, or change runtime/Rust code.

## Focused repair evidence

`_brace_delta` now returns canonical `i64`. The strict retained-Stage-3 native
contract imports and lowers the real `lint_module` implementation with stub
fallback disabled. The final focused attempt rebuilt one module, reused 13
cached modules, reported zero failures, and linked in 2.86 seconds at 160,032
KiB max RSS. Its executable exited 30 with empty stdout and stderr.

Two earlier executable variants exposed the separately claimed EasyFix rule
execution hang. Their production source edits were not expanded into this
repair; the exact HIR contract remains green and bounded.

## Required regression evidence

1. A focused strict Stage 4 route lowers the real `lint_module` rule through
   its registry/implementation ownership without an unresolved type.
2. The real lint-module body, including fixed-width brace-depth arithmetic,
   lowers without relying on a resolver alias for `int`.
3. A fresh full-resource incremental x86 Stage 4 cycle crosses HIR 448 before
   any further blocker is accepted.

## Retained evidence

- `build/bootstrap-stage4-x86-phase4/logs/stage4-fresh1.log`
- `build/bootstrap-stage4-x86-phase4/logs/stage4-fresh1-progress.log`
- `build/bootstrap-stage4-x86-phase4/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`
- `build/focused/stage4-fix-lint-module-hir/contract-attempt3.log`
- `build/focused/stage4-fix-lint-module-hir/contract-attempt3.stdout`
- `build/focused/stage4-fix-lint-module-hir/contract-attempt3.stderr`
