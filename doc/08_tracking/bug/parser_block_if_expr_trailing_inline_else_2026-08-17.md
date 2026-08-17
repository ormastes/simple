# Block-form `if` expression rejects a trailing inline `else:` on the branch body line

**Date:** 2026-08-17
**Status:** OPEN — but the root cause is now LOCATED to an exact function, and a
partial fix was built and measured (it moves the error one token but does not
close it). See "Root cause located" and "Partial fix attempted" below.
**Severity:** MEDIUM — `src/lib/hardware/rv64gc_rtl/imac_protected_core.spl` and
`src/lib/common/crypto/x25519_mlkem768/matrix_receipt.spl` (and every module
importing them) fail to parse
**Found by:** `src/lib/**` parse sweep (7780 files, complete)
**Binary:** `/mnt/data/cgtw2/release/simple` (freshly built Rust seed) — also
fails on the stale deployed binary, so this is not a fresh-build regression

## Minimal reproduction

FAILS — the `if` header opens a block, and the branch body line carries the
`else:` inline at its end:

```simple
fn a4(p: i64, lo: i64) -> i64:
    val v = if p == 1:
        lo else: 9
    v
```

```
error: compile failed: parse: Unexpected token: expected expression, found Else
```

PASSES — same expression with `else:` moved onto its own line at the `if` indent:

```simple
fn a3(p: i64, lo: i64) -> i64:
    val v = if p == 1:
        lo
    else: 9
    v
```

Both the fully-inline form (`val v = if p == 1: lo else: 9`) and the fully-block
form parse; only the mixed form — block-opened header, inline `else` trailing the
indented branch body — is rejected.

## Real-world site

`src/lib/hardware/rv64gc_rtl/imac_protected_core.spl:529-531`:

```simple
            val fault_insn = if state.pipeline_phase == CORE64_FETCH_HIGH:
                state.fetch_low else if state.pipeline_phase == CORE64_FETCH_LOW:
                0 else: state.instruction
```

## Second route: via `elif` (found in the sweep tail, 2026-08-17)

The completed sweep found a second root with the same root cause, reached
through `elif` rather than a plain `if` branch. FAILS:

```simple
fn e1(a: bool, r: text) -> text:
    val v = if a: "" elif r != "":
        r else: "z"
    v
```

PASSES with `else:` moved to its own line:

```simple
fn e2(a: bool, r: text) -> text:
    val v = if a: "" elif r != "":
        r
    else: "z"
    v
```

Real site — `src/lib/common/crypto/x25519_mlkem768/matrix_receipt.spl:697-698`:

```simple
        val admission_reason = if admitted_row: "" elif reason != "":
            reason else: "source-row-public-output-mismatch"
```

So the defect is not specific to `if`/`else if`: any branch body that is opened
as an indented block and then carries a trailing inline `else:` is rejected.

## Expected

`else` / `else if` terminates the current branch body wherever it appears, the
same way it does when it starts a line. The parser currently only recognises it
in statement-leading position after a dedent.

## Re-verified 2026-08-17 (still fails)

Binary: `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
size 59537240, mtime 2026-08-17 12:58:51 UTC.

```
$ bin/simple run r1.spl      # this row's first FAILS fixture, plus a main()
error: compile failed: parse: in ".../r1.spl": Unexpected token: expected expression, found Else
$ bin/simple run r1b.spl     # the `elif` route, second FAILS fixture
error: compile failed: parse: in ".../r1b.spl": Unexpected token: expected expression, found Else
```

Both roots confirmed live. The control (`else:` on its own line) passes.

## Root cause located — exact function

`src/compiler_rust/parser/src/expressions/helpers.rs:168` `fn parse_if_expr`,
block-form branch, statement loop at **`helpers.rs:213-233`**:

```rust
let mut statements = Vec::new();
while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
    while self.check(&TokenKind::Newline) || self.check(&TokenKind::Semicolon) { self.advance(); }
    if self.check(&TokenKind::Dedent) || self.is_at_end() { break; }
    statements.push(self.parse_item()?);          // <-- called on `else`
    ...
}
```

The loop terminates **only** on `Dedent`/EOF. In `lo else: 9` the body's Dedent
has not arrived yet (it follows the `9`), so the loop calls `parse_item()` on
the `Else` token, which bottoms out in the expression parser and produces
`expected expression, found Else`. That is the whole diagnostic — it names
`Else` because `else` really is the token in hand.

**Important structural finding for whoever fixes this:** `parse_if_expr` does
**not** call the shared `parse_block_body`
(`src/compiler_rust/parser/src/parser_impl/core.rs:1137`) — it has its own
inlined copy of the loop. Fixing `parse_block_body` therefore does nothing for
this bug; that was tried first and measured to have no effect on the repro. The
statement form is a third copy (`stmt_parsing/control_flow.rs:433`
`parse_if_expr_after_condition`). Any real fix must account for all three, or
the routes will keep diverging — which is already why this row has "two roots".

Pure-Simple counterpart (same shape, same omission):
`src/compiler/10.frontend/core/parser_stmts.spl:1782` `fn parse_if_expr` —
branch body via `parse_block()` (`parser_stmts.spl:260`), whose loop at
`:272-276` likewise breaks only on kind 182 (Dedent) / 190 (EOF); arm dispatch
for `else`/`elif` is at `:1859-1888`.

## Partial fix attempted, measured, and REVERTED — read before retrying

The obvious minimal fix is to break the loop on `Else`/`Elif`, since neither can
begin a statement. This was implemented at `helpers.rs:219` and built:

```rust
if self.check(&TokenKind::Else) || self.check(&TokenKind::Elif) { break; }
```

Result on a purpose-built binary (isolated worktree, this hunk only,
`cargo build --release --bin simple`):

| fixture | before | with the break |
|---|---|---|
| `r1.spl` (plain `if`) | `expected expression, found Else` | `expected expression, found **Dedent**` |
| `r1b.spl` (`elif` route) | `expected expression, found Else` | parses, then fails at runtime |
| `r1c.spl` (control: `else:` on own line, plus a no-else `if`) | passes | still passes (no regression) |

So the break **is** necessary and does not regress the working forms — the
error advances by exactly one token — but it is **not sufficient**. The residual
is indent bookkeeping: after the terminal `else:` branch is parsed, the
branch-body `Dedent` is still pending and nothing drains it, so the next
expression request meets a `Dedent`. That is the same deferred-dedent machinery
already documented at `helpers.rs:197-205`
(`drain_available_deferred_dedents`, added for multi-line conditions) and
mirrored in the pure-Simple side's `continued_indent` unwind
(`parser_stmts.spl:1890+`).

The change was **reverted** rather than left in the tree: `r1b` moving from a
clean parse error to a *successfully parsed but wrong* program is precisely the
silent-miscompile risk that must not be shipped half-done. **The tree is
unchanged by this investigation.**

### Recommended next step

Add the `Else`/`Elif` break at all three copies AND drain the pending branch-body
dedent after the terminal else, reusing `drain_available_deferred_dedents`.
Verify with all four fixtures above — `r1b` must produce a correct *value*, not
merely parse, since that is where the half-fix went wrong.

## Not worked around

The source was deliberately left unchanged so the repro survives; this is the
same continuation-line-indentation family as
`parser_same_indent_leading_operator_continuation_2026-08-17.md` and
`stage2_multiline_if_continuation_2026-08-14.md`.
