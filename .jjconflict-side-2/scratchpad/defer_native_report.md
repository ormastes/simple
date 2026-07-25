# Bug #172 — native `--entry` build silently drops `defer` (native side)

## Scope achieved

**Option 2** (the task's middle tier): top-level, unconditional `defer`
statements in a function body now run correctly, in LIFO order, at every
`return` in that function (including early returns nested arbitrarily deep
inside `if`/`while`/`for`/`match`) and at fall-off-the-end. Any placement or
construct outside that — `defer` nested inside `if`/`while`/`for`/`match`,
`errdefer` anywhere, or a top-level `defer` combined with a function that
relies on an *implicit* (non-`return`) tail value — is refused with a LOUD,
non-zero-exit build failure instead of a silent drop. Full function-scope
defer (arbitrary nesting of the *registration* itself) was not attempted: it
would require value-capturing the implicit tail expression before running
cleanup, which is a materially larger change than the time budget allowed,
and the task explicitly sanctions falling back to option 2.

Block-form `defer:` (indented multi-statement body) was not touched — the
task scoped verification to the single-statement form the interpreter oracle
handles correctly, and the existing single-line parser (`parser_stmts.spl`)
only feeds `stmt_defer_stmt` a single expression eid regardless.

## Root cause

Two representations of statements coexist in this compiler:
1. The tree-walking **interpreter** uses the tag-based `Stmt`/`STMT_DEFER`
   AST directly (`src/compiler/10.frontend/core/ast_stmt.spl`,
   `.../interpreter/eval_stmts.spl`) — this is why `bin/simple run` executes
   `defer` at all (with its own known, out-of-scope double-execution bug
   inherited from `eval_block` / `call_method_eval` both replaying the same
   depth's defers — confirmed empirically, see Oracle note below).
2. The native **HIR/MIR/codegen** pipeline consumes a different `StmtKind`
   enum (`src/compiler/10.frontend/parser_types_expr.spl:414`) that **has no
   `Defer`/`ErrDefer` variant at all**.

The bridge between the two, `convert_flat_stmt` in
`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`, converts each
raw tag to a `StmtKind` via an `if/elif` chain with no case for
`STMT_DEFER`/`STMT_ERRDEFER` (tags 14 / 15). Every unmatched tag fell to the
final:

```
else:
    return Stmt(kind: StmtKind.Expr(Expr(kind: ExprKind.NilLit, span: span)), span: span)
```

— i.e. `defer <expr>` silently became a no-op `nil` expression statement,
**before HIR lowering ever ran**, with zero diagnostics anywhere. (HIR
lowering's own wildcard case in `statements.spl` — which does call
`self.error("unsupported statement kind", ...)` — was never even reached,
since the bridge had already erased the statement one layer earlier.)

## Fix

All changes are in
`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`:

- New module-level `var g_pending_defers: [Stmt]` — the current function's
  registered-so-far top-level defers, in encounter order (precedented by the
  interpreter's own `eval_defer_eids`/`eval_defer_depths` module globals).
- New `convert_flat_stmt_in_list(idx, is_top_level)` — replaces the bare
  `body.push(convert_flat_stmt(id))` pattern at every statement-list call
  site (function body, `if`-then, `if`-else, `while` body, `for` body,
  `match` arm body, plain `{ }` block). For `STMT_RETURN` it splices the
  *current* `g_pending_defers` (LIFO) immediately before the return,
  regardless of nesting depth — this is what makes early returns inside
  `if`/`while`/`for` correct. For `STMT_DEFER` it either registers into
  `g_pending_defers` (only when `is_top_level`) or returns a loud-fail marker
  (nested). `STMT_ERRDEFER` always returns the loud-fail marker (not
  implemented).
- `convert_flat_stmt` itself gained an explicit `STMT_DEFER`/`STMT_ERRDEFER`
  case (before the generic-fallback `else`) as a defensive catch-all for any
  call site not yet routed through the list helper — never falls through to
  the silent-NilLit path again.
- `convert_decl_fn`'s body-conversion loop now: saves/restores
  `g_pending_defers` around the function (reentrancy safety), calls the list
  helper with `is_top_level: true`, and after the loop replays any
  still-pending defers for the fall-off-the-end case — but **only** when the
  function's true last raw statement was itself `defer` (nothing trails it).
  If the last raw statement was already `STMT_RETURN`, nothing is appended
  (already spliced). If it was anything else (an implicit tail-value
  expression), the build is refused loudly rather than risk silently
  replacing the function's real return value with the defer's value.
- **Loud-fail mechanism**: rather than adding a new fatal-message prefix to
  either allowlist gate, the disallowed cases lower to a reference to a
  deliberately-nonexistent identifier (`__defer_unsupported_placement__`).
  HIR name resolution already rejects this with `"unresolved name: ..."`
  (fatal per `_hir_lowering_error_is_fatal`, `80.driver/driver.spl`), and — as
  independent insurance — MIR expression lowering would separately reject the
  same unresolved reference with `"undefined variable: ..."` (fatal per
  `_mir_error_is_fatal`, `80.driver/driver_pipeline.spl`). No allowlist edits
  were needed or made.

## Oracle note (read before trusting `bin/simple run` diffs)

The interpreter oracle does **not** run single-statement defers correctly —
this contradicts the task's framing. Empirically (worktree
`0b63b447263678959fbc82abf45e76944dac79df`):

```
fn inner() -> i32:
    print("inner-start")
    defer print("inner-deferred")   # single statement, not block-form
    print("inner-end")
    return 0
```

prints `inner-deferred` **twice** whenever `inner` is invoked as a function
call (both when `inner` is `main` itself, invoked by the runtime driver, and
when `inner` is a plain callee). A non-deferred control statement
(`counter = counter + 1`) run the same way increments a counter to `1`
(correct); wrapped in `defer`, the counter becomes `2`. This reproduces with
plain assignment defers too, not just calls — so it is not a print-flush
artifact, and not limited to the documented "block-form" bug. Root cause
(not investigated further, out of scope): `eval_block` and
`call_method_eval` (`10.frontend/core/interpreter/eval.spl` /
`_EvalOps/call_method_eval.spl`) both run a defer-replay pass "mirroring"
each other at function-call boundaries, and both fire.

Given this, oracle stdout was **not** diffed byte-for-byte against native.
Instead, each oracle run was manually de-duplicated to the single-execution,
correct-order expectation (which is unambiguous and consistent across every
test) and native output was compared against that.

## Battery

All run from `/tmp/wt_defer` via
`env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry <file> -o <out> --clean && <out>`.

| # | Case | Oracle (de-duplicated) | Native | Match |
|---|------|------------------------|--------|-------|
| 1 | single defer + prints around it | `start` `end` `deferred` | `start` `end` `deferred` | yes |
| 2 | two stacked defers (LIFO) | `start` `end` `second-registered-first-run` `first-registered-last-run` | same | yes |
| 3 | defer before early return (`if flag: return 1` then `return 0`), called twice | `f-start f-early f-cleanup between f-start f-normal f-cleanup done` | same | yes |
| 4 | two functions each with defers, called from `main` | `start inner-start inner-end inner-deferred after-inner` | same | yes |
| 5 | `errdefer` at top level | n/a (not required correct) | build fails, exit 1, `unresolved name: __defer_unsupported_placement__`, no binary | loud-fail as designed |
| 6 | `defer` nested inside `if` | n/a | build fails, exit 1, same message, no binary | loud-fail as designed |
| 7 | top-level `defer` + implicit (non-`return`) tail value (`fn g() -> i32: defer ...; print(...); 99`) | n/a | build fails, exit 1, same message, no binary | loud-fail as designed (safety guard against silently swapping the return value) |
| 8 | multi-construct: two functions (`a` one defer, `b` two stacked defers), both called from `main` | `a1 a2 a-cleanup b1 b2 b-cleanup-2 b-cleanup-1 main-done` | same | yes |
| 9 | defer + nested `if` mid-body (no return inside), explicit final `return`, called with both flag values | `f-start f-flag f-cleanup f-start f-cleanup done` | same | yes |
| 10 | defer + TRAILING nested `if` as the function's last statement (fall-through, no final `return`; Unit fn) | n/a | build fails, exit 1, same message, no binary | loud-fail as designed (fall-off-end replay is only auto-appended when the last raw stmt is `defer` itself; a trailing `if`/`while`/expr would collide with `lower_hir_block`'s implicit tail-value extraction) |

Test sources are on disk under `/tmp/claude-1000/.../scratchpad/defer_t*.spl`
(same session scratchpad) if re-verification is needed before the worktree is
removed.

## Matrix

`sh scripts/check/native-smoke-matrix.shs` from `/tmp/wt_defer` (run
2026-07-13, with the fix applied): **GATE MET.**

```
total=15 pass=14 fail=1 xfail=0 xpass=0 codegen_fallback_hits=0
```

All 15 cases: (1) arith_fn_call PASS, (2) if_elif_else PASS, (3) while_sum
PASS, (4) for_in_array PASS, (5) array_index_rw PASS, (6) struct_field PASS,
(7) enum_construct PASS, (8) enum_match PASS, (9) string_concat_len PASS,
(10) string_interp PASS, (11) nested_fn_3deep PASS, (12) closure_lambda PASS,
(13) dict_index PASS, (14) option_nil_check **FAIL** (the one allowed
pre-existing failure), (15) result_try_op PASS. Zero codegen fallback hits.

## Files touched

- `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` (only file
  changed; 138 insertions / 8 deletions per `git diff --stat`)

## Deliverables

- Patch: `/home/ormastes/dev/pub/simple/scratchpad/defer_native.patch`
- This report: `/home/ormastes/dev/pub/simple/scratchpad/defer_native_report.md`
