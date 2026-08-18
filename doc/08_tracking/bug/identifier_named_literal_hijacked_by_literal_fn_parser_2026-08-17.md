# A variable named `literal` is hijacked by the `literal fn` parser: "expected Fn, found Assign"

**Date:** 2026-08-17
**Component:** `src/compiler_rust/parser/src/parser_impl/functions.rs` (`parse_literal_function`), `src/compiler_rust/parser/src/token.rs:242` (`TokenKind::Literal`)
**Severity:** P2 — silently unparseable source; the diagnostic points at a
different construct than the actual cause, and cost one push-blocking
investigation most of a session.
**Status:** **FIXED** (verified 2026-08-17 on the seed rebuilt that day)
**Found by:** office lane, while triaging a pre-push guard failure.

## RESOLUTION (2026-08-17) — fixed exactly as recommended, verified

`literal` is now a CONTEXTUAL keyword, the preferred fix recommended below.
The disambiguation is at
`src/compiler_rust/parser/src/parser_impl/core.rs:670-676`:

```rust
TokenKind::Literal => {
    if self.peek_next().kind == TokenKind::Fn {
        self.parse_literal_function()
    } else {
        self.parse_expression_or_assignment()
    }
}
```

i.e. the parser commits to the `literal fn` production only when a `Fn` actually
follows, and otherwise treats `literal` as an ordinary identifier — the same
`peek_next` shape used for `from` immediately below it in that match.

**Binary identity:**
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
size 59537240, mtime 2026-08-17 12:58:51 UTC (Rust seed, rebuilt that day).

**Command and observed output** — the exact FAILS fixture from this row, run per
the Verification note (`run`, not `check`):

```
$ cat kw_bad.spl
fn probe() -> i64:
    var literal = 1
    literal = literal + 1
    literal

fn main() -> i64:
    print("{probe()}\n")
    0
$ bin/simple run kw_bad.spl
2
```

`2` is the correct value, so the name is not merely accepted but bound and
mutated correctly. The `expected Fn, found Assign` diagnostic is gone.

**Still outstanding from this row (NOT done here):** `.claude/rules/language.md`
still does not mention `literal` in its keyword discussion. Since the name is now
contextual it no longer needs to be listed as reserved, so no edit is strictly
required — but the "Note on the documented keyword list" section below is
retained for the record.

The related `identifier_named_grid_hijacked_by_grid_literal_parser_2026-08-09.md`
was NOT re-checked here and may still be open; the general class fix this row
suggested was not attempted — each keyword is still being fixed one at a time.

## Symptom

Declaring an ordinary variable named `literal` makes the whole file fail to
parse, with an error that names a construct the author never wrote:

```
error: compile failed: parse: Unexpected token: expected Fn, found Assign
```

## Minimal repro (both verified 2026-08-17)

FAILS — `bin/simple run kw_bad.spl`:
```simple
fn probe() -> i64:
    var literal = 1
    literal = literal + 1
    literal

fn main() -> i32:
    print("{probe()}")
    0
```
->
```
[INFO] JIT compilation failed, falling back to interpreter: module load error: parse: ... Unexpected token: expected Fn, found Assign
error: compile failed: parse: ... Unexpected token: expected Fn, found Assign
```

PARSES — identical but for the name (`bin/simple run kw_good.spl` prints `2`):
```simple
fn probe() -> i64:
    var const_literal = 1
    const_literal = const_literal + 1
    const_literal
...
```

## Root cause

`literal` is a KEYWORD — `TokenKind::Literal` (`token.rs:242`, commented
"literal (for literal fn definitions)"), used for literal-suffix functions
(`parse_literal_function`, `parser_impl/functions.rs:460`, e.g.
`literal fn _re(s: text) -> Regex:`).

On seeing `literal`, the parser commits to the `literal fn` production and
immediately `expect`s `Fn`. In `var literal = 1` it meets `=` instead and dies
with "expected Fn, found Assign". The message therefore describes the parser's
abandoned hypothesis, not the user's code, and points nowhere near the real
problem. The impl-member `expect(&TokenKind::Fn)` sites are
`types_def/trait_impl_parsing.rs:534`, `parser_impl/functions.rs:90,475`,
`parser_impl/definitions.rs:139`.

## How this was found (why it is worth fixing rather than documenting)

`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` was made unparseable by
a new method `bare_scalar_const_pattern` (landed by `9e78a1b9f9f`) whose body
declares `var literal = HirExpr(...)`. That broke
`scripts/check/check-native-trailing-default-param.shs`, which is wired into the
pre-push hook — so it blocked EVERY push, tree-wide, with an error message that
gave no hint of the cause. Multiple wrong hypotheses were tested first
(multi-line function signatures, `if val` bindings) because the diagnostic
misdirects. The offending method has since been removed from the tree, so the
symptom is currently latent — **it will return the moment that lane re-lands its
feature.**

## Assessment / recommended fix

Make `literal` a CONTEXTUAL keyword, exactly as `move` and `examples`/`and_then`
were on 2026-08-17 (see `.claude/rules/language.md` "Runtime Limitations"):
treat it as the keyword only when a `fn` actually follows, and as an ordinary
identifier otherwise. Both precedents are in
`src/compiler_rust/parser/` and both required a rebuilt seed.

Renaming the variable is a workaround, not the resolution. Per CLAUDE.md —
"When a short, safe grammar or compact expression form fails ... fix it or
record a concrete bug/feature request instead of silently normalizing the
workaround" — this row is that record.

Secondary, cheap mitigation regardless: make the diagnostic name the token it
actually saw (`literal` used as an identifier) instead of "expected Fn".

## Related

- `doc/08_tracking/bug/identifier_named_grid_hijacked_by_grid_literal_parser_2026-08-09.md`
  — same defect CLASS (an identifier swallowed by a literal parser); this is a
  second instance, which suggests the class is worth a general fix rather than
  one keyword at a time.
- `doc/08_tracking/bug/examples_identifier_rejected_in_named_argument_position_2026-08-10.md`
  and `move_identifier_rejected_as_expression_2026-08-15.md` — the two
  contextual-keyword fixes to imitate.

## Note on the documented keyword list

`.claude/rules/language.md` lists reserved keywords as `gen`, `val`, `def`,
`exists`, `actor`, `assert`, `join`, `pass_todo`, `pass_do_nothing`, `pass_dn`,
`examples`, `and_then` — **`literal` is absent**, so a reader following the
rules file has no way to know the name is unsafe. Whoever fixes this should
either make it contextual (preferred) or add it to that list.

## Verification note

Reproduce with `bin/simple run`, NOT `bin/simple check`. The
"Unexpected token: expected X, found Y" diagnostic exists only in the Rust seed
parser (`src/compiler_rust/parser/src/error.rs:73`); `bin/simple check` routes
through the interpreter/self-hosted path and returns **exit 0 with no error**
on a file that is genuinely unparseable. `check` is blind to this entire class
and must not be used as a gate for it.
