# A method call on a parenthesised float literal returns the receiver, not the result

- **Date:** 2026-08-10
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
  `src/compiler_rust/parser/src/expressions/postfix.rs:168` (pre-fix line
  168-170) grabbed ANY following `(...)` as this expression's own call
  parens, with no whitespace-adjacency check (unlike the `LBracket` arm two
  cases below it, which already does check adjacency for exactly this
  reason). So `print (16.0).sqrt()` parsed as `(print(16.0)).sqrt()`:
  `print` fired immediately with the un-rooted `16.0`, then `.sqrt()` was
  applied to (and discarded from) print's return value — hence the observed
  `16.0` with the sqrt silently lost.
- **Lanes:** interpreter and JIT (`SIMPLE_JIT_STRICT=1`) — both, identically.
- **Class:** silent wrong-value. The method is not applied at all.

## Fix (2026-08-11)

Added the same "adjacent to previous token, no whitespace" adjacency check
the `LBracket` postfix arm already used, to the `LParen` postfix arm
(`src/compiler_rust/parser/src/expressions/postfix.rs:168-184`, ~17 lines).
When `(` is NOT adjacent to the callee (i.e. there is a space, as in
`print (16.0).sqrt()`), the postfix loop now `break`s instead of consuming
the parens as a call, deferring to the existing no-paren-call machinery
(`src/compiler_rust/parser/src/expressions/no_paren.rs`,
`parse_with_no_paren_calls` → `parse_single_argument` → `parse_expression`)
which parses `(16.0).sqrt()` as a single self-contained ARGUMENT expression
(parenthesized receiver + full postfix chain), matching the semantics
`f (a).m()` already has anywhere the language expects a no-paren-call
argument (e.g. BDD `expect (a and b) == c`). This is the reading that
matches existing corpus usage of `<callee> (expr)…` space-call forms;
`f(a).m()` with NO space is unaffected and keeps its existing, distinct
"call then chain on the result" meaning (adjacent parens are still consumed
as call args by the same arm).

Truth table (fresh seed build, both lanes; `[fixed]` == this fix):

| probe | pre-fix (RED) | post-fix (GREEN) |
|---|---|---|
| `print (16.0).sqrt()` | `16.0` | `4.0` |
| `identity (16.0).sqrt()` (plain user fn) | `16.0` interp / garbage `2150627075.368833` native | `4.0` both lanes |
| `print (16.0).abs().sqrt()` | `16.0` | `4.0` |
| `print (-9).abs()` (int receiver) | `-9` | `9` |
| `print(16.0).sqrt()` (NO space — unaffected, unrelated shape) | `16.0` then `method sqrt not found on nil` (print returns nil) | same — unchanged, correct per adjacent-call semantics |
| `print ((16.0).sqrt())` (fully parenthesized, workaround) | `4.0` (already worked) | `4.0` (unchanged) |

Verified via a fresh `cargo build --release -p simple-driver` seed binary at
`/mnt/data/cargo-target/release/simple` (both the interpreter lane, plain and
`SIMPLE_JIT_STRICT=1`, and the native AOT lane via `simple compile --native`)
— interpreter and native agree post-fix. Regression sweep green on the same
fresh binary via `SIMPLE_BIN=/mnt/data/cargo-target/release/simple`:
`check-numeric-method-family-dispatch.shs` (28/28),
`check-float-method-argument-position.shs` (34/34),
`check-numeric-builtin-result-type.shs` (48/48, 2 lanes).

## Rediagnosis (2026-08-11)

This is **not** specific to float literals or to `sqrt`. It reproduces for any
receiver wrapped in explicit parens on the RHS of a space-call, with any
method:

```
fn main():
    val b: f64 = 16.0
    print b.sqrt()          # 4.0   correct — no parens around receiver
    print (b).sqrt()        # 16.0  WRONG — same receiver, parens added
```

and it is not print-specific either — `identity (b).sqrt()` (a plain
user-defined single-arg function used the same way) does not even return the
unchanged receiver; it prints a garbage value (`2150627075.368833` measured),
indicating memory corruption in this call shape rather than a simple "chain
dropped" no-op. This looks like a parser/codegen precedence bug in how a
space-call's parenthesized argument interacts with a postfix method-chain
immediately following the closing paren, not a defect in float method dispatch.
**Not fixed in this pass** — out of scope for the sibling fix in
`float_and_int_math_methods_missing_on_numeric_receivers_2026-08-10.md`, which
addressed only genuinely-unresolved math methods, not this parsing/codegen
precedence issue. Workaround: wrap the whole expression in parens —
`print((b).sqrt())` — which is unaffected and returns the correct value.

## Symptom

```
fn main():
    print (16.0).sqrt()      # => 16.0     WRONG, expected 4.0
```

Compare the same method through a local, which is correct once
`float_returning_method_in_argument_position_prints_tagged_bits_2026-08-10.md`
is fixed:

```
fn main():
    val b: f64 = 16.0
    print b.sqrt()           # => 4.0      correct
```

## Why this is a *different* defect from the tagged-bits one

The tagged-bits defect printed `577023702256844800`, which is exactly
`bits(4.0) / 8` — the computation was right and only the boxing was lost. Here
the printed value is `16.0`: a well-formed float, correctly boxed, that is the
**receiver**. `sqrt` was never applied. That is a resolution/lowering failure on
the literal-receiver form, not a type-stamp or boxing failure, and fixing the
type stamp does not touch it.

Found while enumerating the method family for the tagged-bits defect. It is
excluded from `scripts/check/check-float-method-argument-position.shs` on
purpose: that check must go green on the tagged-bits fix, and this row would
keep it red for an unrelated reason.

## Reproduction

```
fn main():
    print (16.0).sqrt()
```
```
simple run repro.spl              # 16.0
SIMPLE_JIT_STRICT=1 simple repro.spl   # 16.0
```

## Related

- `doc/08_tracking/bug/float_returning_method_in_argument_position_prints_tagged_bits_2026-08-10.md`
- `doc/08_tracking/bug/float_and_int_math_methods_missing_on_numeric_receivers_2026-08-10.md`
