# Flat AST Bridge: type-expr index goes stale across an interleaved `ast_reset()`

**Status:** FIXED 2026-07-12 — bounds-check added in `convert_flat_type` before the
expr-arena fallback read; falls back to `TypeKind.Infer` when the index is out
of range (restores pre-#146 behavior for the unrecoverable case).
**Severity:** Blocking — stage-4 native build of the full compiler (`native_build_main.spl`,
`--mode dynload`) dies with `error: semantic: array index out of bounds: index is 48
but length is 13`.
**Affected file:** `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` (`convert_flat_type`, ~line 176)
**Path:** `bug` track.

## Symptom

Running the seed interpreter over the stage-4 build pipeline (parsing
`src/app/io/process_ops.spl`, which declares `extern fn ... -> (text, text, i64)`
at line 8) raised, from the Rust seed's `collections.rs:479` bounds check:

```
error: semantic: array index out of bounds: index is 48 but length is 13
```

## Root Cause

`convert_flat_type(type_expr_idx)` handles the fixed `TYPE_*` tag constants
(≈1-33) and anything `>= TYPE_UNION_BASE` as pre-resolved type tags. Any other
value (the tag-space hole between ~34 and `TYPE_UNION_BASE - 1`) is treated as
a raw index into the shared flat-AST **expr arena** and read directly via
`expr_get_tag(type_expr_idx)` → `expr_tag[idx]` (no bounds check).

For a declared `-> T` return type, that index is captured once at parse time
into `decl_ret_type[idx]` (see `decl_get_ret_type`). `convert_decl_extern_fn`
(convert_nodes.spl:1026-1029) reads it back later, when `flat_ast_to_module`
walks the decl list and converts each extern fn. If a **different** parse job
runs `parser_init_with_path` → `ast_reset()` in between (see
`src/compiler/10.frontend/core/_Ast/module_state.spl:312-420`, which calls
`expr_reset()` → `expr_tag.clear()`), the shared, module-level expr arena is
wiped and refilled with a shorter/different sequence before the stale index is
dereferenced. The arena is process-global (`_AstExpr/nodes.spl:84`,
`var expr_tag: [i64] = []`), not per-file/per-thread, and the stage-4 build
invokes the driver with `--threads 16` across multiple source roots, so a
sibling parse job resetting the arena between "index captured" and "index
consumed" is a real interleaving, not a hypothetical.

This is the same class of hazard the reviewer flagged at 7 other call sites in
`convert_nodes.spl` (lines 599, 751, 758, 887, 910, 1010, 1029) — any
`convert_flat_type` call whose index was captured before the point where it's
finally consumed is exposed whenever an intervening `ast_reset()` can occur.
The extern-fn return type (line 1029) is the one proven to trip it, introduced
by the recent #146 change that started actually threading the extern return
type through (previously discarded, so this path was dead).

When the arena happens to be **longer** after the reset (rather than shorter),
the read stays in-bounds but is **silently stale** — it reads whatever tag now
occupies that slot from the unrelated, later parse job. This is strictly worse
than the OOB crash because it produces wrong-but-plausible output instead of
failing loudly.

## Fix Applied

Investigated moving the extern-fn return-type conversion earlier (eager,
before any possible reset) per the "preferred" fix path. This is not
applicable here: `convert_decl_extern_fn` is already called as early as
architecturally possible for the *current* file — `flat_ast_to_module`'s decl
loop runs immediately after `parse_module_body()` completes for that file, and
no decl branch in the loop (`module_assembly.spl` tag dispatch) recursively
re-parses another file inline. The interleaving comes from *outside* that
scope (a sibling driver/thread parsing a different file), which eager
conversion within the same function cannot prevent — moving the call earlier
does not close the race.

Took the acceptable minimal fix instead: bounds-check `type_expr_idx` against
the live arena length (`expr_count()`, `_AstExpr/nodes.spl:188-192`) before
the `expr_get_tag` read in `convert_flat_type`, and return
`Type(kind: TypeKind.Infer, span: make_span())` when out of range — matching
the pre-#146 behavior for this decl shape.

```
src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl:239-249 (approx, after edit)
    if type_expr_idx >= TYPE_UNION_BASE:
        return Type(kind: TypeKind.Named(type_tag_name(type_expr_idx), []), span: make_span())
    if type_expr_idx >= expr_count():
        return Type(kind: TypeKind.Infer, span: make_span())
    val tag = expr_get_tag(type_expr_idx)
    ...
```

## Residual Risk (documented, not hidden)

This fix only catches the **out-of-range** case. A stale-but-in-bounds read
(arena reset to a length that still covers `type_expr_idx`, now holding an
unrelated expr from a different parse job) is **not** detected or corrected by
this change — `convert_flat_type` will silently return a type built from
whatever tag/text now occupies that slot. The other 6 flagged call sites
(convert_nodes.spl:599, 751, 758, 887, 910, 1010) share the same underlying
hazard and were not touched (out of scope for this fix; each needs its own
audit of whether its captured index can outlive an intervening `ast_reset()`).

The durable fix is either (a) make the flat-AST arena per-file/per-thread
instead of process-global module state, or (b) have the driver serialize
"parse file N" with "convert file N" as one atomic unit across all worker
threads (no other thread's `ast_reset()` may run between them for the same
arena instance). Both are structural changes beyond this bug's scope.

## Secondary Finding (feature request)

The seed interpreter's array-index-out-of-bounds diagnostic
(`collections.rs:479`, `error: semantic: array index out of bounds: index is N
but length is M`) carries no call-stack/location attribution — it took manual
bisection through `convert_flat_type` to find the offending `expr_tag[idx]`
read. Request: thread `DEBUG_CALL_STACK` (or equivalent Simple-frame
attribution) into this specific Rust-side bounds-check panic path so future
OOB errors report which Simple function/line performed the indexing.

## Verification

- `timeout 120 src/compiler_rust/target/bootstrap/simple run <tiny 2-fn .spl>` — still runs correctly (prints `5`).
- `bin/simple test test/01_unit/compiler/frontend/flat_ast_if_else_bridge_spec.spl` — 3/3 pass.
- Full stage-4 gate (`native_build_main.spl --backend cranelift ... --mode dynload`,
  cache cleared first): see report for pass/fail and evidence.
