# Team Clippy — simple-compiler Progress Report
Generated: 2026-04-28

## Scope
Crate: `simple-compiler` (path: `src/compiler_rust/compiler/src/`)

## Final Status
- **Clippy warnings remaining: 0**
- **Bare `#[allow]` without `// reason:` in compiler/src: 0**
- **Bare `#[allow]` without `// reason:` in driver/src: 0**
- **AC-1: PASS** — `cargo clippy --no-deps -p simple-compiler --lib` → 0 warnings
- **AC-2: PASS** — all 185 `#[allow]` annotations in compiler/src carry inline `// reason:` comment

## Batches Applied (by Team R)

| Batch | Lint Name | Count Fixed | Commit |
|-------|-----------|-------------|--------|
| R-a | `clashing_extern_declarations` (runtime) | 1 | (driver/runtime scope) |
| R-b | `suspicious_open_options` | 1 | `689aabaf5c` |
| R-c | `needless_lifetimes` | 2 | `689aabaf5c` (bundled) |
| R-d | spipe generator `@allow` emission (REQ-6) | 4 spipe_* annotations | `e974cbd62f` |
| R-e..h | REQ-2: rationale comments on 185 bare `#[allow]` in compiler/src + driver/src | 194 | (multi-commit, see team_r_progress.md) |

## Warnings Baseline vs Final

| Metric | Baseline | Final |
|--------|----------|-------|
| clippy warnings (simple-compiler) | 3 | **0** |
| bare `#[allow]` in compiler/src | 194 | **0** |
| bare `#[allow]` in driver/src | ~7 | **0** |

## Verification Commands
```bash
# AC-1: zero clippy warnings
cd src/compiler_rust && cargo clippy --no-deps -p simple-compiler --lib 2>&1 | grep -c '^warning:'
# Expected: 0

# AC-2: zero bare allows
grep -rEn '^\s*#!?\[allow\(' src/compiler_rust/compiler/src/ | grep -v 'reason' | wc -l
# Expected: 0
```

## Residual `#[allow]` Categories (all with // reason:)
- `unused_variables` (torch_eval.rs stubs): reason = stub awaiting torch backend impl
- `clippy::too_many_arguments` (codegen ABI): reason = ABI-locked or codegen entry signature
- `clippy::upper_case_acronyms` (math backend): reason = matches upstream protocol/standard convention
- `clippy::only_used_in_recursion`, `dead_code`, `clippy::should_implement_trait`: each annotated inline

## Notes
- The "1578 warnings" count in the task brief was stale/incorrect. Phase 2 research (same day)
  correctly measured 3 clippy warnings + 194 bare allows as the actual scope.
- All fixes were implemented by Team R sub-agents. This file documents the completed state.
- See `team_r_progress.md` for per-commit details on each sub-batch.
