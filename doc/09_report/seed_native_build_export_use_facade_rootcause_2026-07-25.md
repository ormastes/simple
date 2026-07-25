> # RETRACTED 2026-07-25 — this report's conclusion is WRONG.
>
> **A seed built from current `main` DOES native-build and run.** Verified with
> every precondition checked:
> ```
> worktree at 1976a2a3ec5   HAS 3e92fc115116
> cargo rc=0  compiled=2     (genuine rebuild, not a cache hit)
> interning=4                (rt_string_new_literal present)
> probe rc=0  OOB=0
> BINARY: 22928 bytes        RUN: 7
> ```
>
> **What actually blocked native-build:** `3e92fc115116` — "align duplicate
> `CompiledSymbolKind` so native-build resolves" — landed on main at 07:04.
> A one-line enum divergence. `d312b8e4253` was never the blocker.
>
> **Why this report got it wrong:** every failing run behind it was executed in a
> worktree pinned at `d7e0be3d0cd`, created BEFORE 07:04 and therefore missing the
> fix. Eight "reproductions", two patches and four probes all measured a tree that
> lacked the actual fix. The commits were checked for ancestry against `main`, but
> the *worktree under test* was never checked — the wrong axis.
>
> The `export use` facade analysis below may still describe a real gap
> (`.claude/rules/bootstrap.md:154` documents it independently), but it is NOT the
> cause of this failure and nothing here establishes it as such. Treat the
> mechanism as unverified and the conclusion as withdrawn.
>
> Consequence: redeploy is UNBLOCKED. A main-tip seed with interning active is a
> valid bootstrap input. See also: redeploy works on `--backend=cranelift` (~1GB);
> the 50-64GB explosions were the LLVM one-binary path plus a 17,319-process
> fork-bomb, not an intrinsic stage4 ceiling.

# Phase 2 — seed regression `d312b8e4253` root cause

## Verdict: BLOCKED (root-caused, fix NOT landed — two attempted patches verified insufficient)

## Status
`d312b8e4253`'s defer-lazy-imports regression was already partially fixed on
main (`5d9e9b7251b` + `07adf0c25f4`, both ancestors of this worktree's HEAD).
**That fix is INCOMPLETE.** A seed built from main tip still fails native-build
on the simplest possible program, 100% reproducibly, across 8 independent
fresh-cache runs (including 2 after source patches described below).

## Reproduction (confirmed, real end-to-end run, byte-identical across all attempts)

```
fn main():
    print(7)
```

```
$SEED native-build --entry triv.spl --backend cranelift \
  --runtime-bundle core-c-bootstrap --mode one-binary --entry-closure \
  --cache-dir <fresh> -o triv_out

error: semantic: array index out of bounds: index is 0 but length is 0
[STDERR] error: native-build worker exited with code 1.
[STDERR]   interpreter: .../src/compiler_rust/target/bootstrap/simple (exit code 1)
```

`SIMPLE_INTERP_OOB_DEBUG=1` shows the same failing read on every run:
```
[oob-debug] recv=Identifier("expr_tag") idx=Identifier("i")
[oob-debug-bt] 0: interpreter::expr::collections::eval_collection_expr
             1: interpreter::expr::evaluate_expr
             2: interpreter_helpers::patterns::handle_method_call_with_self_update
             ... (repeats ~10x through exec_function/evaluate_call/handle_method_call) ...
             60: interpreter_eval::evaluate_module_impl
```

`expr_tag` (`var expr_tag: [i64] = []`, declared+grown in
`src/compiler/10.frontend/core/_AstExpr/nodes.spl:84,335`) is read as
`val tag = expr_tag[i]` inside `desugar_collections()` in
`src/compiler/10.frontend/desugar/collection_desugar.spl:52`, which imports it
via `use compiler.core.ast_expr.{... expr_tag ...}`. `expr_tag` is non-empty by
the time this runs (parsing already pushed nodes) — the OOB is an aliasing
failure, not a genuinely empty array.

## Investigation (three mechanisms examined, in order)

### 1. Pointer-keyed function-owner map is fragile (real gap, patched, NOT the blocker here)
`CURRENT_EXEC_MODULE` (used by the deferred-import global-read fallback in
`interpreter/expr/literals.rs`) is only set when the executing function has a
recorded owner. Free top-level functions (`Node::Function` in
`interpreter_module/module_evaluator/evaluation_helpers.rs::register_definitions`)
were tagged **only** via a pointer-keyed `FUNCTION_MODULE_OWNER` map
(`Arc::as_ptr` identity), unlike class/struct methods which also get a robust
attribute-based tag (`tag_function_module_owner`) that survives re-Arc-wrapping
(`module_merger.rs` mints fresh `Arc::new(f.clone())`; repeated registration
passes mint more). **Patched**: added the same attribute tag to free functions.
Rebuilt, reran the repro: **byte-identical failure, unchanged.**

### 2. Single-hop binding-chain resolution through re-export facades (real gap, patched, NOT the blocker here)
Instrumented `record_import_binding`/`imported_binding`
(`evaluation_helpers.rs`) — **zero hits** for `expr_tag` across all runs. This
confirmed that code path is not exercised at all for `native-build`'s
flattened/single-binary execution mode; it's used only for the
directly-interpreted/dynamic-`use` mode.

Instrumented the actual consumption site instead
(`interpreter/expr/literals.rs`, `Expr::Identifier` deferred-import fallback).
One run showed:
```
[globread-debug] bindings_for_owner_present=true
  binding_for_name=Some(("...core/ast_expr.spl", "expr_tag"))
[globread-debug] FALLTHROUGH to stale env value; env_val_len=Some(0)
```
`ast_expr.spl` is a **pure re-export facade** (its entire body is `export use
compiler.frontend.core._AstExpr.nodes.*` + one more `export use`) — `expr_tag`
is actually owned by `_AstExpr/nodes.spl`. The binding recorded for the
importer pointed at the facade file itself instead of chasing through to the
true owner, and `MODULE_GLOBALS_BY_OWNER["ast_expr.spl"]` was never populated
(nothing is textually declared in that file), so the read misses and falls
back to the empty snapshot captured at import time. **Patched**: made the read
site in `literals.rs` chase the `MODULE_GLOBAL_BINDINGS_BY_OWNER` chain
transitively (up to 8 hops) instead of trusting a single pre-recorded hop.
Rebuilt, reran the repro: **byte-identical failure, unchanged**, and the
instrumented debug lines from this fix were never reached on the next run
(nondeterministic — see below), meaning the very first binding lookup already
failed rather than needing the extra hops.

### 3. Actual mechanism for this execution mode: closure-discovery does not traverse `export use` (matches a PRE-EXISTING DOCUMENTED gap — most likely true root cause, NOT patched)
Tracing which registration pass actually runs for `native-build --mode
one-binary --entry-closure` (as opposed to `evaluation_helpers.rs`, which
0-hit-instrumented) led to `interpreter_eval.rs`'s own `Node::Function`
handling (~line 394), whose comment states explicitly:

> "This is the only registration pass exercised by the `bin/simple
> run`/`-c` entry path: imports were already flattened into `items` before we
> got here (see `pipeline::module_loader::strip_flattened_import_nodes`),
> which tagged each flattened-in function with its true owning module via a
> synthetic attribute... Functions genuinely defined in the entry/root script
> itself carry no such attribute and fall back to a fixed sentinel `<entry>`."

Global-variable bindings for this same flattened/one-binary mode are recorded
by `record_flattened_import_binding` in `interpreter_eval.rs` (not
`evaluation_helpers.rs`), driven by `FLATTEN_IMPORT_BINDING_MARKER_PREFIX`
marker nodes that the **pipeline flattening pass**
(`src/compiler_rust/compiler/src/pipeline/module_loader.rs`) emits while
walking the import graph. This repo's own `.claude/rules/bootstrap.md`
documents a known, pre-existing gap in exactly this pass:

> "**Native-Build Closure Discovery:** The native-build recursive dependency
> tracer follows plain `use` imports but does NOT traverse `export use`
> shims. Only direct imports trigger cascading closure collection."

`ast_expr.spl` is nothing but two `export use ...*` statements. If the
flattening/closure walker reaches `ast_expr.spl` via some other module's plain
`use compiler.core.ast_expr.{expr_tag}` but does not walk `ast_expr.spl`'s own
`export use ..._AstExpr.nodes.*` edge, it never emits the
`FLATTEN_IMPORT_BINDING_MARKER_PREFIX` marker that would bind
`(ast_expr.spl, expr_tag) -> (nodes.spl, expr_tag)`. `nodes.spl` itself is
still reachable and flattened in (its *functions* work fine —
`expr_count()`, which reads `expr_tag.len()` from **inside** its own owning
module, never fails), but the **global-variable binding chain through the
facade** is permanently, deterministically absent for this symbol/path
combination — independent of registration order, so neither of the two read-side
fixes above can help: there is nothing valid for them to find or chase to.

This is consistent with every observation: the failure is 100% reproducible,
`expr_count()` (same-module read) always works, `expr_tag[i]` (cross-module,
through-facade read) always fails the same way, and both read-side patches
(pointer-identity robustness, transitive chase) left it unchanged because the
gap is upstream of both — in marker *emission*, not resolution.

(One run's non-determinism note: the exact intermediate state observed via
`SIMPLE_INTERP_OOB_DEBUG` differed slightly run-to-run — consistent with the
already-documented seed `Dict.keys()` per-process random iteration order
landmine — but the final user-visible failure was identical on all 8 runs.)

## Patches applied (staged, verified NOT sufficient — kept per instructions so nobody re-derives them)

1. `src/compiler_rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs`
   — tag free top-level functions with `tag_function_module_owner` (attribute,
   travels through Arc re-wraps) in addition to the pre-existing pointer-keyed
   `record_function_owner`, mirroring what class/struct methods already get.
   **Necessary-looking hardening, confirmed NOT the blocker for this repro**
   (this code path isn't even exercised by `native-build`'s flattened mode —
   0 instrumentation hits).
2. `src/compiler_rust/compiler/src/interpreter/expr/literals.rs` — the
   deferred-import global read (`Expr::Identifier` arm) now chases the
   `MODULE_GLOBAL_BINDINGS_BY_OWNER` chain transitively (≤8 hops) instead of
   a single hop, so a binding recorded against a re-export facade module
   still resolves to the true owner if a chain exists. **Real, generally
   correct hardening, confirmed NOT sufficient alone** — the facade's
   glob-reexport binding entry was never created in the first place (root
   cause #3 above), so there is nothing to chase to.

Both patches are staged at
`$BUNDLE/phase2/files/src/compiler_rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs`
and
`$BUNDLE/phase2/files/src/compiler_rust/compiler/src/interpreter/expr/literals.rs`
(also carry harmless `SIMPLE_INTERP_OOB_DEBUG`-gated diagnostic `eprintln!`s
used during this investigation — level-gated, default off, left in place per
the repo's log-retention policy rather than deleted).

## Recommended next step (not attempted — out of this lane's time/cycle budget)

Fix belongs in `src/compiler_rust/compiler/src/pipeline/module_loader.rs`
(`strip_flattened_import_nodes` and the `Node::ExportUseStmt` handling around
lines 1375/1426/1663) plus `interpreter_eval.rs::record_flattened_import_binding`'s
marker contract: when the closure/flattening walker processes a module whose
own body is (or contains) an `export use X.*` re-export, it must also walk
`X` and emit the same `FLATTEN_IMPORT_BINDING_MARKER_PREFIX` glob-binding
markers for `X`'s module-level **global variables** that it already emits for
functions/classes — i.e. extend the documented "does not traverse `export use`
shims" gap-fix (currently scoped to closure *inclusion*) to also cover binding
*chain* emission for globals. This is a pipeline/flattening-stage fix, not an
interpreter-read-side fix — both attempted read-side patches in this lane
confirm the read side is not where the information is missing.

## Bottom line
A seed built from main tip (`d7e0be3d0cd`, this worktree's HEAD) **cannot**
native-build even a trivial `.spl` file. The redeploy-blocking regression is
real, reproduces 100% of the time, and is NOT resolved by either patch applied
in this lane. Root cause is most likely the pre-existing, documented
`export use` closure-discovery gap in the pipeline flattening stage, now shown
to also break global-variable binding-chain resolution (not just closure
inclusion) — confirmed via targeted runtime instrumentation, not fixed here.
