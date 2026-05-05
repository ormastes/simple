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

## 2026-05-05 Update

Status: still blocked.

New evidence from `build/os/bootstrap/simpleos-x86_64/stage1/simple native-build --backend llvm --source ./src/compiler/10.frontend/core/ast_types.spl --entry ./src/app/cli/bootstrap_main.spl`:

- The stage1 binary can parse source text through the bootstrap lexer/parser path.
- Env-backed declaration tags are populated correctly; e.g. `SIMPLE_BOOTSTRAP_DECL_TAG_0=3`.
- Imported i64 and array-return accessors are not reliable in the generated stage1 binary:
  - `decl_get_tag(0)` returns literal `3` internally but arrives as `nil` at the flat bridge call site.
  - `decl_get_fields(0).len()` and related array-return helpers produce corrupt lengths.
  - Formatting some i64 values through `print "...{value}"` crashes in `rt_value_to_string`.
- Avoiding i64 debug formatting and using env-backed tag text lets the bridge process all ten declarations in `src/app/cli/bootstrap_main.spl`.
- With temporary minimal function shells and skipped import/struct materialization, parsing reaches:
  - `[BOOTSTRAP-PHASE] phase2:parse:done`
  - `[BOOTSTRAP-PHASE] phase3:hir_typecheck:start`
- It then segfaults in `driver__driver__CompilerDriver_dot_lower_and_check_impl`.

Current blocker:

The Simple-generated stage1 compiler is not yet trustworthy for cross-module accessor ABI, array-return values, dictionary/module materialization, or HIR lowering. The temporary flat-bridge simplifications are diagnostic only and are not acceptable as the final fix because they discard function bodies, imports, structs, and fields.

Additional 2026-05-05 evidence:

- `bin/simple run src/os/port/bootstrap_cross.spl -- --status` no longer
  reports the leftover 5,968-byte Stage 2 artifact as built. It now reports:
  `stage 1: BUILT (14 MB)` and `stage 2: invalid-small (5968 bytes)`.
- The latest `bootstrap_cross.log` retry path reaches
  `aot:weave_aop:done` and fails with
  `Codegen error in native-build: Linking failed: No object files to link`.
- The older `bootstrap_cross_nostrip.log` path still records the `llvm-lib`
  Stage 2 segmentation fault.

Additional focused bootstrap probes:

- A freshly rebuilt stage1 compiler from the current worktree initially
  segfaulted before `main` in
  `__module_init_backend__backend__llvm_backend_tools`. GDB showed the crash at
  the module initializer store for the mutable top-level text
  `_llvm_bootstrap_last_object_path`.
- `src/compiler/70.backend/backend/llvm_backend_tools.spl` no longer keeps that
  path in mutable module state; `llvm_bootstrap_last_object_path()` now
  recomputes the deterministic temp object path from `_get_temp_dir()` and
  `getpid()`. After this change a rebuilt stage1 compiler passes
  `/tmp/simple_stage1_patch2/simple --version`.
- The next stage2 probe with that rebuilt stage1 still does not emit a
  compiler. It now segfaults earlier during phase 2 parsing:
  `frontend.flat_ast_bridge.flat_ast_to_module()` while parsing
  `./src/app/cli/bootstrap_main.spl`.
- The Cranelift adapter was also tightened to read back emitted object bytes
  instead of returning `CodegenOutput.object(..., [])`, and to lower
  `unwrap`/`unwrap_err`/`unwrap_or` method calls to their receiver in the direct
  bootstrap path. This passed `bin/simple check` but has not yet been proven by
  a successful stage2 build because the fresh stage1 now crashes first in the
  flat AST bridge.
- A later rebuilt stage1 with the flat bridge mutable reset removed reaches
  `phase2:parse:done` and enters HIR lowering. The next failures are all in the
  stage1-generated bootstrap data handoff:
  - `ParserModule.functions` direct field access segfaults after
    `[hir-lower] functions:map`.
  - `Dict.keys()` on the destructured function map segfaults after
    `[hir-lower] functions:keys`.
  - Looking up a known env-backed function name in that map segfaults after
    `[hir-lower] function:name bootstrap_version`.
  - Reusing a flat-bridge function cache without resetting it corrupts the array
    length (`functions:count -1`).
- Current conclusion: stage2 is blocked by stage1 runtime/codegen corruption for
  arrays, dictionaries, and struct field handoff between flat parsing and HIR
  lowering. The OS/QEMU smoke lanes remain separate; this is now a pure
  self-hosting compiler payload blocker.

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

## 2026-05-05 Follow-Up Evidence

- Empty stage2 output was traced to bootstrap AOT skipping MIR lowering with `mir_ok = true`; the driver must route bootstrap mode through `bootstrap_lower_to_mir_context()`.
- `ctx.hir_modules["app.cli.bootstrap_main"]` / `module.functions[SymbolId]` lookup is unsafe in compiled stage1 bootstrap and segfaults after `[mir-lower] function-symbol`.
- The safer path is `bootstrap_lower_hir_globals_to_mir_module()`, using `_bootstrap_hir_functions` populated during HIR lowering.
- With the HIR-global MIR path and `SIMPLE_BOOTSTRAP_REAL_LOWER=1`, stage2 progressed to real MIR lowering and then crashed while lowering `native_build_help`; additional `real-lower:*` probes were added around signature/body/end_function to isolate that next substep.
- Current checked state: `src/compiler/50.mir/mir_lowering.spl` and `src/compiler/80.driver/driver.spl` pass `bin/simple check ... --clean`; stage2 still does not produce a runnable compiler.
