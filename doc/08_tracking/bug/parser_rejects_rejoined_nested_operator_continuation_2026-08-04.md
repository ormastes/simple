# Parser rejects a continuation that rejoins the outer chain after nesting deeper

**Status:** FIXED 2026-08-04 (seed parser)
**Found:** 2026-08-04
**Component:** parser (indent/continuation handling)
**Impact:** blocks module load for 33 files in the x25519mlkem768 campaign

## Symptom

`Unexpected token: expected expression, found Dedent`, reported against the file
being imported. Because an unresolved `use` is only a WARN, the importing program
still runs and prints its own output — so this reads as a passing run unless you
grep the log for `Dedent`.

## Minimal reproduction

Fails (10 lines, no imports):

```
fn g(x: text) -> text:
    x
fn f(a: text, b: text) -> bool:
    a == b and
        a ==
            g(b) and
        a ==
            g(b)
fn main():
    print("A {f(\"x\",\"x\")}")
```

Run: `bin/simple run a.spl` → `parse: Unexpected token: expected expression, found Dedent`

## What actually triggers it

The trigger is **a continuation that nests deeper and then rejoins the outer
continuation level, twice**. It is not any of the things it first looks like:

| variant | result |
|---|---|
| single nested continuation (`a == b and` / `a ==` / `g(b)`) | **parses** |
| same body with an explicit `return` | **parses** |
| multi-line function signature | irrelevant — parses either way |
| **two** nested continuations rejoined by `and` | **FAILS** |

So the parser accepts descending into a deeper continuation indent, but not
returning to the shallower continuation indent and then descending again. Adding
parentheses around each nested comparison fixes it:

```
    a == b and
        (a ==
            g(b)) and
        (a ==
            g(b))
```

This is consistent with the documented rule in `.claude/rules/language.md`
("Multi-line booleans — wrap in parentheses"), but that rule reads as advice
about a single wrapped condition; it does not say that a *rejoined* nested
continuation is unrepresentable without parens. The failure mode is also silent
at `simple check`, which exits 0 on the same file.

## Scale

A scan of the 90 campaign `.spl` files for this shape (operator-terminated line →
deeper-indented line → line that dedents back but not past the statement indent)
reports **326 candidate sites across 33 files**. That count is an upper bound —
occurrences inside parentheses are legal, and the detector cannot tell them
apart — but the parse failures are real and sequential: fixing the first site in
`measurement_qualification.spl:190-193` moved the failure to the next module.

Worst-affected files by candidate count: `performance_attestation.spl` (58),
`qualified_timing.spl` (27), `matrix_receipt.spl` (26),
`x25519mlkem768_coverage_receipt.spl` (24), `x25519mlkem768_gpu_binding.spl` (22).

## Why this matters beyond one campaign

None of the x25519mlkem768 unit specs can execute while the modules they import
fail to parse, so every timing/attestation assertion in that campaign is
currently unreachable. Any spec run over them reports a load failure, not a
result — and since the underlying `use` failure is only a WARN, a careless read
of the output looks like success.

## Fix options

1. Parser: allow a continuation to dedent back to a previously-established
   continuation level while an operator context is still open. Preferred — the
   source is readable and the current rejection is arbitrary.
2. Source: parenthesize each nested comparison at all real sites. Mechanical but
   large, and it bakes a parser limitation into 33 crypto files.

Option 1 first; option 2 only for sites that need to build before the parser
lands.

## Fix as landed

Option 1 (parser). `skip_newlines_and_indents_for_method_chain`
(`src/compiler_rust/parser/src/parser_helpers.rs`) now also absorbs a `Dedent`
that merely rejoins a continuation level this expression already entered. Every
caller invokes it immediately after consuming a binary operator, so an operand
must follow and a `Dedent` there is the chain stepping back out of a deeper
sub-continuation — not the end of the expression.

Absorption is **credit-bounded**: a `Dedent` is consumed only while the
expression still holds an unmatched `Indent` (locally, else in
`binary_indent_count`, decrementing whichever supplied the credit). A `Dedent`
that closes the enclosing *block* is therefore never eaten, and the
INDENT/DEDENT books stay balanced for `consume_dedents_for_method_chain`.

Option 2 (source parenthesisation) was applied to
`measurement_qualification.spl` first, then **reverted** once the parser fix
landed — the original unparenthesised source now parses, so the workaround is
not baked into the crypto files.

## Evidence

- `simple-parser` suite: **266 lib tests passed, 0 failed** (254 pre-existing,
  4 in `rejoined_continuation_test.rs`, 8 in `multiline_shapes_test.rs`), plus
  every integration binary green. `cargo clippy` reports 0 warnings/errors.
- The new tests are **not vacuous**. Reverting the rejoin fix turns exactly its
  2 bug-shape tests RED while its 2 guards stay green. Reverting the other four
  fix sites turns 5 of the 8 `multiline_shapes` tests RED and leaves 3 guards
  green.
- Whole-campaign parse scan over the 90 `.spl` files, source workaround
  reverted: **90 ok / 0 failing**, down from 15 failing at the start
  (15 → 9 → 4 → 2 → 0 as each defect landed).
- My fixes introduced **no** new failures: the post-fix failing set was verified
  a strict subset of the pre-fix set at every step (`comm -13 before after`
  empty).

## The other 9 — three further defects, now also fixed

The survivors were unrelated to the rejoin bug. Each was reduced to a minimal
repro, fixed, and covered in `parser/src/multiline_shapes_test.rs`. Campaign
parse status went **15 → 9 → 4 → 2 → 0 of 90 failing**.

**1. Consecutive trailing-`=` continuations** (6 files) —
`expected expression, found Assign`.
`parse_expression_or_assignment` drained the continuation's DEDENT *before*
scanning for no-paren call arguments. The drain also consumes the RHS line's
terminating Newline, erasing the statement boundary, so the no-paren scan saw
the *next statement* and swallowed it as an argument list, then choked on its
`=`. One continuation alone parsed, because EOF or a keyword-led statement gave
the scan nothing to eat. Fix: run the no-paren scan first, while the Newline is
still visible (`expressions/no_paren.rs`).

**2. Trailing-`->` signature continuation** (1 file) —
`expected identifier, found Newline`.
`fn f(...) ->` with the return type on the next line. The *leading* form
(`->` starting the next line) was handled; the trailing one called `parse_type`
with a Newline current. Fix: skip newlines/indents after the arrow, and drain
the balancing DEDENT after the signature's `:` and Newline — the token stream
there is `Dedent Indent <body>`, so the drain has to happen at the body, not at
`parse_type` (`parser_impl/functions.rs`).

**3. Inline `if cond: <assignment>`** (1 file) —
`expected expression, found Assign`.
The block form always worked; the inline form parsed its body with
`parse_expression`, which cannot represent an assignment. Fix: parse the inline
body with `parse_expression_or_assignment` and, when it yields a statement,
finish as a statement-form `IfStmt` with single-statement blocks, including
inline `else` / `elif` / `else if` (`stmt_parsing/control_flow.rs`).

**4. `if`-expression with a multi-line condition** (2 files) —
`expected Indent, found Dedent`.
`val x = if a == p and\n        b == q:` — the statement-form `if` drained the
compensating DEDENT (the "Deep" case on `drain_available_deferred_dedents`) but
the expression form did not, so it met the DEDENT where it wanted the body's
INDENT. Fix: same drain in `parse_if_expr` (`expressions/helpers.rs`).

Fixing 2 also repaired a pre-existing break in the *leading*-arrow form: the
`other_arrow_forms_still_parse` guard fails on the unfixed parser.

## Verification notes

- `simple check <file>` exits 0 on the failing file — do not use it as the oracle.
- Reproduce with a driver that imports the module and grep the output for
  `Dedent`; exit status alone is fail-open.
- The fix is in the **Rust seed** parser, which is what currently runs as
  `bin/simple`. The pure-Simple parser does not emit this message and was not
  changed; if it grows the same continuation handling it needs the same
  credit-bounded rule.
