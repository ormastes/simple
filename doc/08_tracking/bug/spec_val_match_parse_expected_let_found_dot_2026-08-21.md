# `val x = match ...` inside a spec makes a later method call fail to parse

- **Filed:** 2026-08-21
- **Status:** RESOLVED 2026-08-21 (root-caused; `match` was incidental)
- **Binary:** `bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed)

## Symptom

A spec containing `val ok = match <expr>:` parses only in a narrow shape.
Adding statement-level method calls around it (`ghost.set("status", "x")`,
`assert_true(reported.contains("lost write"))`) makes the WHOLE FILE fail with:

```
error: compile failed: parse: in "<spec>.spl": Unexpected token: expected Let, found Dot
```

The message names no line, and the file parses again as soon as the example is
removed — which is how it was localized at all. The same example in a file of
its own, with the match arms returning bare `true` / `false` and no method call
on the bound value, parses and passes.

## Why it is filed rather than normalized

Per `.claude/rules` a short, safe form that fails to compile must be fixed or
recorded, never silently worked around. It cost real time here: the reproduce
coverage for
`doc/08_tracking/bug/test_db_update_row_keys_nonexistent_id_column_2026-08-21.md`
had to be split into `test/01_unit/lib/database/sdn_lost_write_spec.spl` and
stripped of its message assertions to get it to parse.

## Not yet isolated

The exact trigger was not narrowed to a minimal pair — several variants were
tried (renaming the binding, `expect(...)` vs `assert_true(...)`, string vs bool
arms, tuple destructuring elsewhere in the file) and all of the failing ones
share only "a `val` bound from a `match` plus a `.`-call in the same example".
Next step for whoever picks this up: bisect against the parser rather than the
spec, since the error is raised before any spec semantics run.

## Root cause (2026-08-21)

Not `match` at all — the `match` in the failing example was a coincidence. The
trigger is the identifier `ghost` in `ghost.set("status", "x")`.

`mut`, `shared` and `ghost` are lexed as keywords. The seed's statement
dispatcher (`src/compiler_rust/parser/src/parser_impl/core.rs`) routed the bare
keyword unconditionally to `parse_mut_let` / `parse_shared_let` /
`parse_ghost_let`, and **all three `expect(&TokenKind::Let)` as their second
token** (`stmt_parsing/var_decl.rs:29,35,149,159`). So any statement starting
with a variable named `ghost`/`shared`/`mut` died with
`Unexpected token: expected Let, found Dot` — a whole-file parse error with no
line number, which is why it looked like it came from the neighbouring `val x =
match`.

The general rule that was wrong: these are declaration prefixes only in the
two-token forms `mut let` / `shared let` / `ghost let`. Fixed by gating the
three dispatch arms on `peek_is(&TokenKind::Let)`, exactly the disambiguation
pattern already used in the same `match` for `lazy` (`is_lazy_decl`), `common`
(`is_common_use`), `mock` (`is_mock_decl`) and `literal`. Unmatched keywords now
fall through to `parse_expression_or_assignment`, which already accepted them.

Scope: **seed only**. The self-hosted frontend (`src/compiler/10.frontend/`) has
no `ghost`/`shared` keyword, so it never had this defect — no file there was
touched.

## Minimal reproduce

```
class Box:
    var status: text = ""
    fn set(k: text, v: text):
        self.status = v

fn main():
    val ghost = Box()
    ghost.set("status", "x")
    println(ghost.status)
```

No `match`, no `val`-from-match. Fails pre-fix with the reported error.

## Evidence

Spec: `test/01_unit/compiler/parser/decl_prefix_keyword_as_identifier_spec.spl`
(6 examples: `ghost.method()`, `shared` as a var name, `val x = match` + `.len()`
+ `.to_upper()` chained on the result, `val x = if …`, a match expression in
argument position with `.len()` chained, and both together in one example).

Before (deployed seed at the time of filing):

```
error: compile failed: parse: in ".../decl_prefix_keyword_as_identifier_spec.spl": Unexpected token: expected Let, found Dot
Results: 1 total, 0 passed, 1 failed
```

After (seed rebuilt with the fix and redeployed to
`bin/release/x86_64-unknown-linux-gnu/simple`, 59677736 bytes, 2026-08-21 02:36):

```
SPEC FILE VERDICT: ... outcome=OK declared>=6 executed=6 passed=6 failed=0 skipped=0 dropped=0
Results: 6 total, 6 passed, 0 failed
```

Seed parser regression suite on the fixed build:
`cargo test --release -p simple-parser` -> **TOTAL passed=1069 failed=0**.
Existing parser specs re-run sequentially on the deployed binary:
`cast_less_than_spec.spl` `Results: 2 total, 2 passed, 0 failed`,
`common_mistake_function_identifier_spec.spl` `Results: 3 total, 3 passed, 0 failed`.

## Follow-up

`test/01_unit/lib/database/sdn_lost_write_spec.spl` was split and stripped of
its message assertions to work around this; it can now be reunified with the
`doc/08_tracking/bug/test_db_update_row_keys_nonexistent_id_column_2026-08-21.md`
reproduce coverage. Left as a TODO for that bug's owner, not done here.
