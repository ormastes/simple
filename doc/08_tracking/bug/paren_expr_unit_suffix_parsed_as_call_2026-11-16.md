# Unit suffix on a parenthesized expression parsed as a call (`(n)_fbytes`)

Found 2026-11-16 (lane rb4-parensuffix). `doc/07_guide/language/type_system.md`
(lines ~288-306) documents `(self.value() / 1000)_s`, `(n * 1000)_ms`,
`(user_id.value() + 1)_uid` as the conversion idiom. On the seed:

```
unit FreeBytes: i64 as fbytes
val n = 5
val b = (n)_fbytes     # semantic: function `n` not found
```

Cause: the lexer only attaches a unit suffix to a literal. After `(n)` the
grouping collapsed to `n`, and the following identifier `_fbytes` was taken as
a no-paren call argument (`n _fbytes`). The pure-Simple parser silently
returned the bare group (no multiply, suffix dropped).

Decision: the guide form is intended (it is the only way to put a unit on a
computed value, and no spec expects `)_ident` to be rejected), so the parsers
were fixed, not the guide.

## Fix
Both parsers desugar a suffix identifier `_<alpha>...` glued to the `)` of a
non-tuple group (no whitespace) to `expr * 1_sfx`, reusing the literal unit path:
- seed: `src/compiler_rust/parser/src/expressions/primary/collections.rs`
  (`apply_paren_unit_suffix`, span adjacency `previous.end == current.start`).
- pure Simple: `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl`
  (same line, column = `)` column + 1).
Limit: a multiply desugar only fits numeric families (`_ip`-style string units
are out of scope). `f(n)_sfx` (call result + suffix) is not covered.

Spec: `test/01_unit/compiler/frontend/paren_expr_unit_suffix_spec.spl`
- before (deployed seed): `outcome=ERROR executed=0 ... reason=parse-error`;
  pure-Simple parse examples fail without the frontend change (`binaries=0`).
- after (rebuilt seed): `outcome=OK declared>=6 executed=6 passed=6 failed=0`.

Separate observation (not fixed here): `==` on two unit values returns a
unit-wrapped bool (`5 * 1_fbytes == 5_fbytes` prints `true_fbytes`).

Status: verification-pending
