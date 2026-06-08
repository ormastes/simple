# Pure-Simple Bootstrap Stage2 Remaining

> Status: PARTIAL — BLOCKED: stage2 is blocked by stage1 runtime/codegen corruption during type lowering; stage2 build exists but cannot emit; next step is re-capture from live run with tighter phase-2 tracing (2026-05-20 audit)

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

## 2026-06-07 Update

Status: still blocked for the pure-Simple stage2 payload.

Current repo bootstrap verification passes through the wrapper path:

```bash
SIMPLE_BOOTSTRAP=1 SIMPLE_LIB=src ./bin/simple build bootstrap --seed=./bin/simple
```

Evidence captured on 2026-06-07:

- Stage 1, Stage 2, and Stage 3 all emitted 26 KB artifacts.
- All three stages matched hash
  `718fe35b4d36937744d7481b96cacd74e1905a54f1bcdf6ebd1f4d2da1d169a3`.

That is useful bootstrap determinism evidence, but it is not the same as the
pure-Simple stage2 compiler payload in this plan. A direct probe of the
documented pure-stage2 command shape was run from `src/compiler_rust`:

```bash
target/bootstrap/simple native-build \
  --backend llvm-lib \
  --source ../compiler \
  --source ../app \
  --source ../lib \
  --source ../compiler_shared \
  --entry ../app/cli/bootstrap_main.spl \
  -o /tmp/simple_stage2_probe
```

It exited `1`, emitted no `/tmp/simple_stage2_probe`, and failed with:

```text
error: bootstrap_main cannot emit a seed-wrapper fallback for /tmp/simple_stage2_probe
error: rebuild with the full Simple driver so native-build uses real Simple lowering/codegen
```

Current conclusion: Rust remains the bootstrap seed and host substrate. The
pure-Simple stage2 work is still open until `native-build` reaches real Simple
lowering/codegen for this entry instead of stopping at the seed-wrapper
fallback guard.

Additional 2026-06-07 dispatch evidence:

- The default command still takes the protected Simple-first path and still
  refuses to emit a seed-wrapper fallback for `/tmp/simple_stage2_probe_default`.
  This keeps accidental fallback artifacts blocked.
- With `SIMPLE_NATIVE_BUILD_RUST=1`, the same `native-build --backend llvm-lib`
  command bypasses the seed-wrapper guard and reaches the Rust native-build
  handler.
- That probe still exits `1` and emits no artifact because the bootstrap seed
  reports:
  `error: native backend 'llvm' is not available in this build; rebuild the Rust driver with --features llvm or use --backend cranelift`.

Current conclusion after the dispatch check: the seed-wrapper fallback is now
avoidable for diagnostic probes, but the pure-stage2 payload still cannot emit
until the probe runs with an LLVM-capable bootstrap seed or the plan accepts a
Cranelift-compatible stage2 probe.

Additional 2026-06-07 pure-Simple Stage2 lowering evidence:

- The direct `target/bootstrap/simple native-build --backend llvm-lib ...`
  probe now reaches the Simple-first lowering/JIT path instead of stopping at
  the seed-wrapper fallback guard.
- Rust remains the bootstrap seed and diagnostic host. The seed lowerer was
  hardened to report function/source context for index-type inference failures,
  which made subsequent pure-Simple blocker capture actionable.
- Cleared Stage2 lowering blockers in this pass include:
  - backend/runtime enum compatibility and `Value.Nil` unit-return lowering
  - LLVM-lib, LLVM adapter, Cranelift adapter, and backend-helper public import
    visibility
  - compiler SFFI cache/context stale generated names and discarded `push`
    results
  - object-taker mutable cache helpers and inference-context parameter typing
  - trait coherence reserved `gen` binding
  - monomorphization substitution/table/mangling stale generated names
- The latest probe still exits `1`, emits no
  `/tmp/simple_stage2_probe_default`, and currently stops at:

```text
HIR lowering error: Parameter 'template_name' in function 'mangle' requires explicit type annotation
```

Current conclusion after this pass: the pure-Simple Stage2 path is no longer
blocked at dispatch or backend facade visibility. It is now progressing through
ordinary Simple source lowering defects, mostly stale generated helper names,
missing explicit parameter annotations, and mutable-state helper declarations.
The next concrete fix is the monomorphization metadata `mangle(...)`
parameter typing blocker.

## Next Steps

### A. Route the pure-stage2 probe through the full Simple driver

The current direct `target/bootstrap/simple native-build ...` probe stops before
the older parse/HIR failure because the bootstrap entry refuses to emit a
seed-wrapper fallback. The next probe must first ensure the command is running
the full Simple driver path that owns real Simple lowering/codegen.

Acceptance:
- the command no longer fails with `bootstrap_main cannot emit a seed-wrapper fallback`
- either `/tmp/simple_stage2` is emitted
- or the next exact lowering/codegen failure is captured
- if using `SIMPLE_NATIVE_BUILD_RUST=1`, the selected seed must include the
  requested backend or the probe must explicitly switch to a supported backend

### B. Capture the next post-parse-start failure cleanly

Once the full-driver path is active, use a file-backed run so the final exit
code and trailing diagnostics are preserved:

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

### C. If parse-phase failure remains opaque, tighten phase-2 instrumentation

Primary target:
- `src/compiler/10.frontend/flat_ast_bridge.spl`

Suggested instrumentation:
- log current source path at module entry
- log just before returning the built frontend module
- log around the first HIR entry that consumes the returned frontend `Module`

Goal:
- determine whether the next failure is still in flat AST conversion, module construction, or the first HIR consumer

### D. Check for remaining `Module` collisions if the same shape error returns

Primary files:
- `src/compiler/10.frontend/parser_types.spl`
- `src/compiler/10.frontend/ast.spl`
- `src/compiler/20.hir/hir_lowering/items.spl`
- `src/compiler/20.hir/hir.spl`

Specific question:
- after the explicit `FrontendModule(...)` constructor change, does any downstream parameter or local still infer against `ast.Module` rather than `parser_types.Module`?

### E. Once stage2 emits, proceed immediately to stage3 verification

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

## 2026-06-07 Follow-Up Evidence

- `native-build --backend llvm-lib` now dispatches through
  `src/app/cli/native_build_main.spl` for the Simple-first path instead of
  stopping at the protected seed-wrapper fallback.
- The stage2 probe now clears the earlier blockers for:
  - flat bridge alias collisions (`ParserFunction`)
  - legacy `has_T` optional annotations
  - wildcard let bindings
  - in-body extern and function-scope import registration
  - driver API static calls through `CompilerDriver`
  - same-name `Span` layout collisions in combined JIT lowering
  - generated parser helper artifacts in `parser_types_utils.spl` and
    `parser_types_expr.spl`
- Latest probe:

```bash
cd src/compiler_rust
target/bootstrap/simple native-build \
  --backend llvm-lib \
  --source ../compiler \
  --source ../app \
  --source ../lib \
  --source ../compiler_shared \
  --entry ../app/cli/bootstrap_main.spl \
  -o /tmp/simple_stage2_probe_default
```

Earlier result from the first 2026-06-07 pass:

```text
stage2_exit=1
no_stage2_artifact
HIR lowering error: Unknown variable: fields_len while lowering compute_transparent_layout
```

Later 2026-06-07 follow-up fixed and checked the subsequent blockers for:

- `fields_len(...)` helper-call artifacts in transparent type layout.
- target-architecture pointer/bit helper availability during type layout.
- shorthand easy-fix filters and callback/loop field inference in the stdlib and
  compiler fix-rule copies.
- missing `std.text.levenshtein_distance`.
- missing `FixConfidence.Certain`.
- missing `input_line` declaration for the interactive fix CLI path.
- HIR diagnostics now include the owning function for missing parameter type
  annotations, which made the `each` callback blocker actionable.

Latest probe after those fixes still exits `1`, emits no stage2 artifact, and
now stops at:

```text
HIR lowering error: Unsupported feature: cannot infer field type while lowering ThemeRegistry.resolve_surface: struct 'ResolvedThemeColors' field 'surface_level_0'
```

Current next blocker: type the `ThemeRegistry.resolve_surface` field-access path
or teach HIR lowering the `ResolvedThemeColors` field type in that path, then
continue the same stage2 probe loop.

## 2026-06-07 Stage2 Linker/Instantiation Follow-Up

The next focused pass continued from `origin/main` commit `30e5b3a9fd` in a
clean worktree because the shared checkout had unrelated dirty files and
submodule state.

The stage2 probe now clears the subsequent linker and instantiation blockers
for:

- missing explicit parameter types in `TemplateInstantiator.mangle`,
  `instantiate`, and `is_cached`
- stale generated helper calls around instantiation caches, result unwrapping,
  linker object-template caches, and recorded-instantiation appends
- immutable `SmfReaderImpl.read_note_sdn` even though the method closes over
  mutable reader state
- stale `notesdnmetadata_new`, `lazyinstantiationresult_*`,
  `linkercompilationcontext_from_objects`, and `instantiator_instantiate`
  helper names in lazy link-time instantiation
- impossible `SymbolBinding.Undefined` checks in linker unresolved-symbol
  detection
- dict destructuring in `Linker.write_native_output`
- backend/platform `SystemLinker` enum name collision during HIR lowering
- unsupported `range(0, code_len)` use in `write_elf_object`

Latest probe still exits `1`, emits no stage2 artifact, and now stops at:

```text
HIR lowering error: Cannot infer type: Cast { expr: Binary { op: BitAnd, left: Identifier("value"), right: Integer(255) }, target_type: Simple("u8") } while lowering u16_to_bytes
```

Current next blocker: make SMF header little-endian byte helpers lowerable in
stage2 without relying on unsupported `u8` casts/method conversion, or teach
HIR lowering to infer these `u8` conversions.
