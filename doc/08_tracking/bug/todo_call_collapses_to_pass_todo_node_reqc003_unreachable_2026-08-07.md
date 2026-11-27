# `todo(...)` parses into the same AST node as `pass_todo(...)`; REQC003's dedicated branch is unreachable from real source
## RESOLVED 2026-09-13 (fix b5a8b492fce) — re-verified 2026-11-25, see Resolution section at bottom

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

## Resolution 2026-11-25 (re-verification; original resolution 2026-09-13 lost in tree transplant)

**Status: RESOLVED.** The code fix landed on release/1.0.0 as commit
`b5a8b492fce` (2026-09-13, "fix(compiler): make real todo(...) calls
reachable by REQC003") with the doc-resolution commit `72273f89975`. A later
rebase/tree-transplant (`88aac2ffe28`) restored this document to its
2026-08-17 open state while keeping the code fix, so the resolution text is
re-recorded here with fresh 2026-11-25 verification evidence.

**Option chosen:** a runtime-identical variant of option 1. Instead of
emitting a real `expr_call(expr_ident("todo", ...), ...)` node (which would
change what the interpreter and MIR lowering see for every existing
`todo(...)` in the tree), the parser keeps the shared tag-40
(`EXPR_PASS_TODO`) node but routes real `todo(...)` calls through a new
constructor `expr_pass_todo_call()` (`_AstExpr/accessors.spl`), which marks
the node's `int` field with `1`. `check_required_comment`
(`required_comment.spl`, `is_any_pass` branch) reads that marker and applies
the REQC003 two-string (`"what | hint"` split) check instead of REQC001's
single-string check. The `int` field was used, not `extra`, because several
generic AST walkers (`unused_vars.spl`, `closure_analysis.spl`,
`call_edge_utils.spl`, `alloc_inference.spl`) recurse into `extra` as an
optional child-expression index whenever it is >= 0.

**Runtime-semantics evidence (unchanged):**

- Both `pass_todo(...)` and `todo(...)` still produce tag 40; the marker is
  metadata only. Interpreter: `interpreter/eval.spl:610`
  `if tag == EXPR_PASS_TODO: return val_make_nil()` — no branch on the
  marker. Flat-AST/MIR bridge: `_FlatAstBridge/convert_nodes.spl:1324`
  handles tag 40 uniformly with the other pass variants.
- Live run 2026-11-25 (`SIMPLE_LIB=src bin/simple.exe run --mode=interpreter`):
  `fn f() -> i64:` with body `todo("fix")` then `7`, `print f()` prints `7`
  — `todo(...)` is still an evaluation no-op.

**Blast radius (grep 2026-11-25):** ~38 hits in `src/`, ~25 in `test/` for a
bare `todo(` call shape. Most are string literals inside lint/fix-rule
sources; real statement-position calls exist (e.g.
`todo("handle remaining cases")` in `src/lib/common/spec/evidence/model.spl`,
`src/plugins/backend_c/**`). All keep identical AST tag and runtime
semantics; the only observable change is the lint diagnostic code
(REQC001 -> REQC003, both severity `warn`) for weak single-string `todo(...)`.

**Before/after lint output** (repro `fn f():` / `todo("fix")`):

- Before (pinned by the pre-fix regression probe and this doc's Reproduction
  section): `warning[REQC001]: pass_* used without a comment string`.
- After (live 2026-11-25, `SIMPLE_LIB=src bin/simple.exe lint repro.spl`):
  `warning[REQC003]: todo used without what-remains and next-step strings in
  \`f\`` / `hint: Use todo("what remains", "hint or issue")`.
- Well-formed `todo("add validation", "see issue 42")`: no REQC warning.
- Bare `pass_todo("later")` keyword: still REQC001, not REQC003 (plus the
  unrelated pre-existing STUB003 placeholder error).

**Spec results 2026-11-25** (`SIMPLE_LIB=src bin/simple.exe test <spec>
--mode=interpreter`):

- `test/01_unit/compiler/lint/required_comment_cli_spec.spl`: 11 total,
  8 passed, 3 failed, 2 skipped. ALL REQC003 probes pass, including "emits
  REQC003 (not REQC001) through lint_cli_source for a weak bare todo(...)",
  the well-formed-todo negative case, and the pass_todo-keyword-still-REQC001
  case. The 3 failures are the `Linter.lint_source` describe block
  (REQC001/REQC003/REQC004) — pre-existing on the unmodified base and
  unrelated to this fix: after WP-7 the REQC00x loop lives only in
  `lint_cli_source`, so `Linter.lint_source` (no AST decls) no longer emits
  REQC codes, contradicting those older examples.
- `test/01_unit/compiler/semantics/lint/required_comment_lint_spec.spl`:
  FAILS AT LOAD (0 examples executed), pre-existing and unrelated:
  `Module "compiler.frontend.core" does not export 'if_chain_nodes'`. The
  spec imports `flat_if_stmt_chain_new` / `ARM_VALUE_BIND` / etc. from an
  `if_chain_nodes` module that no longer exists anywhere under
  `src/compiler/10.frontend/` (its API survives only in this spec, used by
  the REQC004 if-chain tests ~lines 363-410). Same error was already noted
  as pre-existing in the 2026-09-13 resolution. Repairing it means rewriting
  those REQC004 if-binding examples against the current AST API — tracked
  separately under
  `doc/08_tracking/bug/reqc004_if_binding_wildcard_unimplemented_2026-10-30.md`,
  out of scope for this bug.

- Status: RESOLVED (code fix 2026-09-13 `b5a8b492fce`; re-verified and
  resolution re-recorded 2026-11-25)
