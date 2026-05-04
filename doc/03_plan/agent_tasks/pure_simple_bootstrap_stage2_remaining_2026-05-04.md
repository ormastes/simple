# Pure-Simple Bootstrap Stage2 Remaining

Status: active
Date: 2026-05-04

## Goal

Get the pure-Simple stage2 bootstrap build to emit a working artifact:

```bash
cd src/compiler_rust
target/bootstrap/simple native-build \
  --backend llvm-lib \
  --source ../compiler \
  --source ../app \
  --source ../lib \
  --source ../compiler_shared \
  --entry ../app/cli/bootstrap_main.spl \
  -o /tmp/simple_stage2
```

This plan covers the remaining work after the recent bootstrap parser/bridge fixes.

## Current State

- Stage2 no longer fails immediately on bootstrap CLI routing.
- Stage2 no longer fails on missing bootstrap driver externs.
- Stage2 no longer fails on the earlier parser-surface gaps such as `parse_expr not found`.
- Stage2 no longer fails on the flat bridge out-of-bounds caused by encoded type tag `1000` (`TYPE_NAMED_BASE`).
- Stage2 no longer fails at the earlier `parser_module_new` path with `class Module has no field named imports`.
- The latest clean run reaches:
  - `[BOOTSTRAP-PHASE] phase1:load_sources:done`
  - `[BOOTSTRAP-PHASE] phase2:parse:start`
- The build still does not emit `/tmp/simple_stage2`.

## Recently Cleared Blockers

### 1. Parser facade visibility

Fixed in:
- `src/compiler/10.frontend/core/parser.spl`
- `src/compiler/10.frontend/core/parser_decls_use.spl`

What changed:
- `compiler.core.parser` now re-exports the split parser expr/stmts/decls surfaces it already imports.
- `parser_decls_use.spl` now imports `parse_expr` directly from `compiler.frontend.core.parser_expr`.

Why it mattered:
- Bootstrap resolution still depended heavily on the `compiler.core.parser` facade.
- Missing re-exports surfaced as `semantic: function 'parse_expr' not found`.

### 2. Flat bridge encoded type-tag crash

Fixed in:
- `src/compiler/10.frontend/flat_ast_bridge.spl`

What changed:
- `convert_flat_type(...)` now handles encoded core type tags before touching `expr_tag[...]`.
- The bridge now recognizes encoded tags such as:
  - `TYPE_NAMED_BASE + id`
  - `TYPE_OPTION*`
  - `TYPE_RESULT`
  - `TYPE_FUTURE`
  - `TYPE_POLL`
  - `TYPE_TASK`
  - `TYPE_DICT`
  - `TYPE_FN`

Why it mattered:
- `parser_parse_type()` returns encoded type tags, not always flat expr indices.
- The prior bridge treated `ret=1000` as an expr index and crashed out of bounds.

### 3. Frontend `Module` constructor collision

Mitigated in:
- `src/compiler/10.frontend/flat_ast_bridge.spl`

What changed:
- The flat bridge now constructs the module through the explicit `FrontendModule(...)` alias instead of the helper path that still constructed a bare `Module(...)`.

Why it mattered:
- There are multiple `Module` types in the frontend tree.
- The old path could resolve to the wrong `Module` shape and fail with:
  - `class Module has no field named imports`

## Remaining Problem

The stage2 bootstrap still stops during or after `phase2:parse:start`, but the latest captured log tail does not yet show the next concrete semantic or runtime failure after the `FrontendModule(...)` disambiguation.

So the current gap is no longer a known one-line surface miss. The next blocker must be re-captured from the live stage2 run with tighter phase-2 tracing.

## Next Steps

### A. Capture the next post-parse-start failure cleanly

Use a file-backed run so the final exit code and trailing diagnostics are preserved:

```bash
cd src/compiler_rust
rm -f /tmp/stage2_bootstrap.log /tmp/simple_stage2
target/bootstrap/simple native-build \
  --backend llvm-lib \
  --source ../compiler \
  --source ../app \
  --source ../lib \
  --source ../compiler_shared \
  --entry ../app/cli/bootstrap_main.spl \
  -o /tmp/simple_stage2 \
  >/tmp/stage2_bootstrap.log 2>&1
echo $?
tail -n 200 /tmp/stage2_bootstrap.log
```

Acceptance:
- either `/tmp/simple_stage2` is emitted
- or the next exact failure line is captured after `phase2:parse:start`

### B. If parse-phase failure remains opaque, tighten phase-2 instrumentation

Primary target:
- `src/compiler/10.frontend/flat_ast_bridge.spl`

Suggested instrumentation:
- log current source path at module entry
- log just before returning the built frontend module
- log around the first HIR entry that consumes the returned frontend `Module`

Goal:
- determine whether the next failure is still in flat AST conversion, module construction, or the first HIR consumer

### C. Check for remaining `Module` collisions if the same shape error returns

Primary files:
- `src/compiler/10.frontend/parser_types.spl`
- `src/compiler/10.frontend/ast.spl`
- `src/compiler/20.hir/hir_lowering/items.spl`
- `src/compiler/20.hir/hir.spl`

Specific question:
- after the explicit `FrontendModule(...)` constructor change, does any downstream parameter or local still infer against `ast.Module` rather than `parser_types.Module`?

### D. Once stage2 emits, proceed immediately to stage3 verification

Run:

```bash
/tmp/simple_stage2 native-build \
  --backend llvm-lib \
  --source src/compiler \
  --source src/app \
  --source src/lib \
  --entry src/app/cli/main.spl \
  -o bin/simple
```

Then verify:
- `bin/simple --help`
- one small interpreter smoke
- one small native-build smoke

## Non-Goals For This Tranche

- No broader Rust runtime/codegen cleanup.
- No DB/native query work.
- No generalized migration of deprecated generic/index syntax warnings.
- No broad parser API redesign beyond what stage2 requires to emit.

## Exit Criteria

This plan is done when:

1. `target/bootstrap/simple native-build ... -o /tmp/simple_stage2` succeeds.
2. `/tmp/simple_stage2` is runnable.
3. Stage3 can produce `bin/simple`, or the next blocking stage3 failure is captured as a separate focused plan.
