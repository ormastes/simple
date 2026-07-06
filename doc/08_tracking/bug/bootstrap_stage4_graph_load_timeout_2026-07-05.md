---
id: bootstrap_stage4_graph_load_timeout_2026-07-05
status: OPEN
severity: high
discovered: 2026-07-05
discovered_by: Stage-4 bootstrap execution on Apple M4
related: scripts/bootstrap/bootstrap-from-scratch.sh
related: build/bootstrap/logs/aarch64-apple-darwin/stage4-native-build.log
---

# Stage-4 Bootstrap: Native-build graph loading exceeds default 7200s timeout

## Summary

Stage-4 bootstrap's interpreted native-build worker exceeded the default 7200-second (2-hour) timeout on Apple M4. The module graph loading phase alone consumed approximately 97 minutes before reaching parse/compile phases, indicating a severe performance bottleneck in dependency resolution and module discovery.

## Evidence

- Platform: Apple M4 (aarch64-apple-darwin)
- Build stage: Stage 4 (pure-Simple self-hosted)
- Phase that timed out: Module graph loading
- Time spent in graph loading: ~97 minutes (before parse/compile)
- Default timeout: 7200 seconds
- Log location: `build/bootstrap/logs/aarch64-apple-darwin/stage4-native-build.log`

## Impact

Stage-4 bootstrap remains incomplete and cannot produce a fresh pure-Simple binary. The long timeout blocks verification builds and prevents rapid iteration on bootstrap fixes.

## Scope

The issue is in the module graph loading phase (`compiler/99.loader/module_graph.spl` or similar), likely:
- Quadratic or worse complexity in dependency resolution
- Redundant graph traversals
- Missing memoization or caching of module metadata
- Inefficient file I/O during discovery

`bootstrap-from-scratch.sh:430` currently passes no `--timeout` argument, so the native-build worker uses a hardcoded default that is insufficient for the current graph-loading performance.

## Next Steps

1. Profile the native-build module graph loading phase to identify the bottleneck (dependency resolution, disk I/O, algorithm complexity).
2. Add memoization/caching for module metadata queries.
3. Either fix the underlying performance issue or add a configurable `--timeout` parameter to `bootstrap-from-scratch.sh` with a reasonable default for typical hardware (e.g., 14400+ seconds for interpreted stage-4).

## Status update 2026-07-06

The error message's recommended fix — "use the in-process backend for cross-target builds" — was tried and does NOT help for the full-CLI stage-4 build on Apple M4. Running the stage-4 build via the in-process path (deployed self-hosted `bin/simple native-build --backend llvm-lib --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/cli/main.spl`, WITHOUT `SIMPLE_BOOTSTRAP`/`--timeout` so `native_build_main.spl` dispatches straight to `cli_native_build` in-process instead of spawning the interpreted worker) was left running for ~91 minutes and STILL had not reached codegen:

- No output binary was produced (`build/bootstrap/full/aarch64-apple-darwin-macho/simple` never appeared).
- At 91 min the process was still in the parse / HIR-lowering phase, emitting `[parser_error]` lines against core compiler sources (`src/compiler/mir_opt/mir_opt/pattern_dispatch.spl`, `src/compiler/hir/hir_lowering/_Items/declaration_lowering.spl`, `src/compiler/tools/fix/rules/impl_/lint_code.spl`, `src/std/nogc_sync_mut/env/variables.spl`). Graph-load + full-source parse is the bottleneck; the in-process path shares it because it still loads and parses the entire import graph before any codegen.
- Conclusion: switching interpreted-worker → in-process does NOT bypass the graph-load/parse cost for the full-CLI source set. The real fixes remain the profiling/memoization items above (and/or a self-hosted-parser investigation into why so many core files raise parser errors under this build path).

Consequence for the `browser` subcommand: the currently deployed binary `bin/release/aarch64-apple-darwin-macho/simple` (Jul 5 14:16) predates the `browser` subcommand wiring, so `bin/simple browser --help` still returns `error: file not found: browser`. No rebuild could be produced within budget, so the binary was left untouched (backup NOT taken, nothing deployed — deploy stayed clean).

Working fallback for users TODAY (Approach C, verified on the deployed binary): the browser app entry is runnable directly as a file —
`bin/simple src/app/ui.browser/main.spl <file.ui.sdn> --open` (dispatches, `--help`/`--open`/`--dry-run` all work). The `browser` and `ui.browser` bare subcommands do NOT dispatch on this binary; only the direct-file path does.
