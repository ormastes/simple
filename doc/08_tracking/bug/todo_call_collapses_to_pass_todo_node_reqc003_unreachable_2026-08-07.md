# `todo(...)` parses into the same AST node as `pass_todo(...)`; REQC003's dedicated branch is unreachable from real source

**Status:** OPEN (unverified 2026-09-12)

**Filed:** 2026-08-07 · **Severity:** low (coverage gap, not silent-wrong-data — a
weak `todo(...)` still gets flagged, just as REQC001 instead of REQC003)
**Found by:** WP-7 of `doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md`
(wiring `compiler.semantics.lint.required_comment.check_required_comment`
into `lint_cli_source` and deleting the text-based REQC00x reimplementation
in `lint_checks.spl`)

## What's wrong

The parser desugars a bare `todo(...)` call (both statement position,
`parser_stmts.spl:595-598`, and expression position,
`_ParserPrimary/primary_expr.spl:399-405`) into `expr_pass_todo(msg, 0)` —
**the exact same AST node tag** (`EXPR_PASS_TODO`, tag 40) that `pass_todo(...)`
itself produces. There is no `expr_call` node with callee identifier `"todo"`
for real parsed source; both `"what remains"` and `"hint or issue"` string
arguments (if given) are pre-joined by `parse_optional_rationale_args()`
(`parser_stmts.spl:89-104`) into one combined `msg` string (`"what | hint"`)
before the AST node is even created.

`check_required_comment` (`src/compiler/35.semantics/lint/required_comment.spl:233-256`)
has a dedicated REQC003 branch that looks for `tag == 9` (a call expr) whose
callee is an `expr_ident` named `"todo"`, then separately validates
`args[0]`/`args[1]` as two distinct string-literal arguments. That shape is
never produced by the real parser for `todo(...)` — it only exists today
because the direct unit spec
(`test/01_unit/compiler/semantics/lint/required_comment_lint_spec.spl`,
"REQC003 todo detection" describe block) constructs the `expr_call` shape by
hand via `expr_call(expr_ident("todo", 0), [...], 0)`, bypassing the parser
entirely.

Consequence: a weak `todo("fix")` in real source is flagged (correctly, in
the sense that *something* fires), but as **REQC001** (`pass_* used without a
comment string`) via the `is_any_pass` branch operating on the combined `msg`,
not as **REQC003** (`todo used without what-remains and next-step strings`).
The REQC003 message ("todo used without what-remains and next-step strings")
is more specific/actionable and is now unreachable from real source.

## Why this surfaced now

The now-deleted TEXT reimplementation in `lint_checks.spl`
(`check_required_comment_source`, removed by WP-7) matched raw source text
(`normalized.starts_with("todo(")`) independent of the AST, so it emitted
REQC003 regardless of how the parser structured the node. Wiring the real
`bin/simple lint` output path to the AST-based `check_required_comment`
(entry_and_fixes.spl) and deleting that text twin is net-correct per WP-7 (no
more double diagnostics, real predicate instead of a `<10`-chars text
heuristic) but exposes this pre-existing parser/checker shape mismatch:
REQC003 was previously reachable only because the deleted checker did not
consult the AST at all.

## Reproduction

```simple
fn f():
    todo("fix")
```

`lint_cli_source(Linter.new(), "sample.spl", source)` on this input returns
REQC001, not REQC003. See
`test/01_unit/compiler/lint/required_comment_cli_spec.spl` ("emits REQC001
(not REQC003) through lint_cli_source for a weak bare todo(...)") for the
regression probe pinning this exact behavior.

## Fix options (not done here — out of WP-7's stated file scope)

1. Have the parser build a real `expr_call(expr_ident("todo", ...), [what, hint], ...)`
   node instead of collapsing into `expr_pass_todo`, so REQC001 and REQC003
   stay distinguishable at the AST level (most correct, touches the parser).
2. Or drop the REQC003-specific branch and accept that a weak `todo(...)` is
   just a REQC001 pass_* violation with a less specific message (least
   invasive, loses the "what remains and next-step" wording).

## Unblock condition

A WP that deliberately touches `parser_stmts.spl` /
`_ParserPrimary/primary_expr.spl` `todo(...)` parsing (option 1) or
`required_comment.spl`'s REQC003 branch + its unit spec (option 2).

## Re-verification 2026-08-17

Re-read current source. Unchanged:

- `src/compiler/10.frontend/core/parser_stmts.spl:656`: `return stmt_expr_stmt(expr_pass_todo(msg, 0), 0)` —
  `todo(...)` still collapses to `expr_pass_todo`, not a real `expr_call`.
- `src/compiler/35.semantics/lint/required_comment.spl:233-256` (current line numbers
  match doc verbatim): the `tag == 9` / callee-name `"todo"` REQC003 branch is still
  present, correctly implemented, and still unreachable from real parser output for
  exactly the reason filed.

Fix option 1 (parser emits a real `expr_call` for `todo(...)`) requires editing
`src/compiler/10.frontend/**`, which is out of this worker's scope lock
(`30.types, 35.semantics, 90.tools, 95.interp` only). Fix option 2 (drop the
REQC003 branch, accept REQC001-only) is in-scope but was explicitly rejected by
the filer as a regression in diagnostic quality ("loses the wording"), so not
applied unilaterally here.

**Verdict: BLOCKED (real fix is in `10.frontend`, out of scope for this worker).**
No code change made in this pass.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.

## Resolution 2026-09-13

Fixed via option 1 (parser distinguishes the two forms), touching
`10.frontend` after all — the prior worker's scope lock was specific to
that worker's own task, not a repo-wide constraint.

Added `expr_pass_todo_call()` in `_AstExpr/accessors.spl`: same node shape
as `expr_pass_todo` (tag 40), but marks the node's `int` field with `1` so
`check_required_comment` can tell "this source literally wrote `todo(...)`"
from "this source used the `pass_todo` keyword" — both still produce the
same tag, but are now distinguishable. Wired into both real parse sites
(`parser_stmts.spl` statement position, `_ParserPrimary/primary_expr.spl`
expression position). `required_comment.spl`'s `is_any_pass` branch now
checks that marker and, when set, splits the message on `" | "` (the
existing `parse_optional_rationale_args` join separator) and applies the
REQC003 two-string check instead of REQC001's single-string check.

Deliberately did NOT use the `extra` field (my first attempt): several
generic AST walkers (`unused_vars.spl`'s `collect_refs_in_expr`,
`closure_analysis.spl`, `call_edge_utils.spl`, `alloc_inference.spl`, and
`required_comment.spl`'s own `_check_expr`) treat `expr_get_extra` as an
optional child-expression index and recurse into it unconditionally
whenever it is `>= 0` — repurposing it as a boolean flag would have made
every one of them walk into whatever unrelated node sits at arena index 1.
Caught this by reading those walkers before shipping, reverted the
`extra`-based attempt, and used the node's `int` field instead (no
generic-recursion contract; precedent: `expr_mark_string_processed`
already reuses it as a per-tag marker).

Updated the regression-pinning spec
(`test/01_unit/compiler/lint/required_comment_cli_spec.spl`) from
asserting the bug ("emits REQC001 (not REQC003)") to asserting the fix
("emits REQC003 (not REQC001)"), added a well-formed-todo negative case
and a pass_todo-keyword-still-REQC001 case.

```
test/01_unit/compiler/lint/required_comment_cli_spec.spl:
10 total, 8 passed, 2 failed
```

The 2 remaining failures are pre-existing and unrelated (REQC004 if-val/
if-var wildcard-binding admission, `Module compiler.frontend.core does not
export 'if_chain_nodes'`) — confirmed present before this change too via a
`git checkout` / `git apply` round trip that isolated just this fix's
files. No regression in `unused_vars_spec.spl` (6/6).

- Status: RESOLVED (2026-09-13) — 37e69573ecc, spec `test/01_unit/compiler/lint/required_comment_cli_spec.spl`
