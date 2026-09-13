# `expect(x).not.to_<matcher>(...)` — a supported chain form, but only under native compilation

- Status: OPEN, thoroughly diagnosed, deliberately not fixed this round (see "Why not fixed" below)
- Binary: `d4c0779cef6cf0cc4054` / rebuilt `57761d4fbfed5e444a36` (neither carries a fix for this)
- Base: `work/unit-p1-2026-09-13` at `d2887f81bf2`
- Affects: **61 spec files, 244 call sites** across `test/01_unit` (exhaustive count:
  `grep -rohE '\.not\.to_[a-zA-Z_]+' test/ src/` — 3 distinct matcher spellings in
  use: `.not.to_contain` (237), `.not.to_equal` (6), `.not.to_be_nil` (1))

## What this is, precisely

`expect(x).not.to_contain(y)` is a DELIBERATE, documented, tested language
feature — not a typo. Proof:
`test/01_unit/compiler/bdd_negated_matcher_chain_lowering_spec.spl` is a
regression spec written specifically to fix this exact chain form for
NATIVE COMPILATION, with acceptance criteria "`bin/simple compile
<this file>` rc=0 and all four examples pass" (fixed suite4, 2026-08-31, see
that file's own header comment). It passes under `bin/simple compile`.

**It fails under the interpreter**, with:
```
semantic: undefined field: unknown property or method 'not' on String
```
Minimal repro (confirmed on both `d4c0779c…` and the round-3 rebuild):
```
use std.spec.{describe, it, expect}
describe "not chain":
    it "not.to_contain is honoured":
        val s = "hello world"
        expect(s).not.to_contain("zzz")
```
`bin/simple test <this file>` -> `1 failed`, that exact message.
`bin/simple compile <this file>` -> also fails (different reason: the file
needs interpreter-only test-runner scaffolding to link), which is WHY the
interpreter path is reached for real specs at all: most `_spec.spl` files
that use this chain also use other interpreter-only constructs, fail native
compilation, and fall back to `bin/simple run <original source>` — completely
unmodified, per `test_runner_execute.spl:594` fb_reason text: "degraded to
plain interpreter execution of the original source."

## Root cause — one code path has the feature, the other never got it

**Compiled path** (works): `stmt_lowering.rs::try_lower_bdd_matcher_statement`
(line 3228) calls `peel_expect_matcher_receiver` (line 3201) on the AST
BEFORE evaluating anything — it recognises `Expr::FieldAccess { receiver,
field: "not" }` as the receiver of the outer `MethodCall`/`FieldAccess`, peels
it, and negates the resulting predicate.

**Interpreter path** (broken): the interpreter's method-call dispatch
(`interpreter/expr/calls.rs::eval_call_expr`, `Expr::MethodCall` arm at line
152) has NO equivalent peeling. It evaluates the receiver expression to a
VALUE first (in this case `.not` gets evaluated as an ordinary field access on
the STRING `s`, since `expect(s)` apparently returns the plain value in
whatever path leads here), and only afterwards tries to dispatch a method call
on that value — by which point the information "this receiver chain started
with `expect(...)` and had a `.not` link" is gone. `interpreter_method/mod.rs`
DOES already implement the negated forms as literal method names —
`to_not_equal` / `to_not_contain` / `to_not_include` / `to_not_be_nil`
(lines 637-690) — so the underlying assertion logic exists; only the
`.not.to_X` -> `to_not_X` translation is missing on this path.

## Dead ends investigated (so the next agent doesn't retread them)

1. **`execution.rs::rewrite_method_expect_line`** (Rust driver,
   `src/compiler_rust/driver/src/cli/test_runner/execution.rs`) already
   textually rewrites a `not_()` (function-call spelling) prefix — looked
   like a ready-made fix site. It is NOT: this function is called only from
   `preprocess_spipe_file`/`preprocess_matchers_only`, which are part of a
   **Rust-native CLI test-runner code path that `bin/simple test` does not
   use**. The live orchestration is pure Simple
   (`src/app/test_runner_new/test_runner_main.spl`, confirmed by the
   "Simple Test Runner v0.8.1" banner string existing ONLY there). Editing
   `execution.rs` changes nothing observable; a first attempt this round did
   exactly this, verified it had zero effect on the repro above, and was
   reverted before committing.
2. **The pure-Simple mirror**,
   `src/app/test_runner_new/test_runner_execute.spl::spipe_rewrite_method_expect_line`
   (line 253) — this IS live code, but it lives inside `preprocess_spipe_file`
   (line 372, docstring: "Wrap SPipe file content in fn main() for native
   compilation"), i.e. it only runs on the NATIVE-COMPILE attempt. The
   interpreter fallback explicitly reruns the file as `["run", file_path]` —
   the raw path, not the preprocessed one (`test_runner_execute.spl:578,594`)
   — so this rewrite never reaches interpreted execution either.
3. **`std.spec`'s `expect()`** (`src/lib/nogc_sync_mut/spec.spl:734`) returns
   `i64`, not a chainable Expectation object — `expect(...).matcher(...)` is
   NOT plain user-level Simple method dispatch on that return value at all;
   both the HIR lowering and the interpreter treat `expect(...).<matcher>` as
   a compiler-special form (confirmed by `stmt_lowering.rs`'s own comment:
   "In compiled mode, describe/it/expect are intercepted at HIR lowering and
   never reach user-defined fn expect"). This rules out fixing it by editing
   `std.spec.spl` alone.

## The real fix location, for whoever picks this up

`interpreter/expr/calls.rs::eval_call_expr`, the `Expr::MethodCall { receiver,
method, args, .. }` arm (starts line 152). Before any of the existing
`Identifier`/`FieldAccess`-on-identifier special cases run, detect: `receiver
== Expr::FieldAccess { receiver: inner, field: "not" }` where `inner`
ultimately traces to an `expect(...)` call (mirror
`peel_expect_matcher_receiver`'s exact recognition, don't re-derive it) — if
matched, evaluate `inner`, then dispatch `to_not_<method_without_to_prefix>`
(or equivalent) against it using the SAME logic `interpreter_method/mod.rs`'s
`to_not_equal`/`to_not_contain`/`to_not_be_nil` arms already implement,
instead of falling into the generic field-access-then-method-call path that
currently produces the error above.

## Why not fixed this round

`eval_call_expr`'s `Expr::MethodCall` arm is ~400+ lines of interleaved,
heavily-commented special-case dispatch for mutation/ownership semantics
(in-place Array mutators, `me` self-update write-back, nested field-access
receivers) — several of the existing comments explicitly warn about
infinite-recursion traps between this function and
`interpreter_helpers::patterns` if a new branch is routed incorrectly. A
correct fix needs to intercept the `.not`-FieldAccess-receiver shape BEFORE
those existing branches misinterpret it (in particular the `Expr::FieldAccess
{ receiver: outer_receiver, field }` branch at line 252, whose
`Expr::Identifier` sub-check would simply fall through for our case since
`outer_receiver` is a `Call`, not an `Identifier` — its fallthrough behaviour
past that point was not traced far enough to be confident it is safe to graft
onto). This is real interpreter-completeness work needing careful review and
its own test matrix, not a same-day textual-rewrite fix — filed rather than
risked, per this lane's own precedent
(`java_new_hint_fires_after_named_arg_colon_2026-09-13.md`).

## Impact if left unfixed

61 spec files' `.not.to_X(...)` assertions never execute when those specs
fall back to interpretation (the common case — most of them use other
interpreter-only constructs). This does not mean those files show 0 examples;
the runner still runs the file and other assertions in it, but every `.not.`
line raises `semantic: undefined field...` mid-example, typically failing the
enclosing `it` block. Not a data-loss-style silent-pass risk — it fails
loudly, every time, at ERROR severity, exactly like the JavaNew case's
diagnostic-quality standard.
