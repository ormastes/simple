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

- `simple-parser` unit suite: **258 passed, 0 failed** (254 pre-existing + 4 new
  in `parser/src/rejoined_continuation_test.rs`). `cargo fmt --check` exit 0,
  `cargo clippy` clean.
- The new tests are **not vacuous**: reverting the fix and re-running turns
  exactly the 2 bug-shape tests RED (`rejoined_nested_continuation_parses`,
  `observation_matches_shape_parses`) while the 2 guard tests stay green.
- Whole-campaign parse scan over the 90 `.spl` files, with the source workaround
  reverted: **81 ok / 9 failing**, improved from **15 failing** before the fix.

## Remaining 9 — different defects, not this one

The survivors fail with unrelated errors and need separate triage:

- `expected expression, found Assign` — `x25519mlkem768_candidate_batch_measurement.spl:535`,
  `x25519mlkem768_coverage_receipt.spl:406`, `x25519mlkem768_gpu_dispatch.spl:270`,
  `x25519mlkem768_measurement_qualification_spec.spl:330`,
  `x25519mlkem768_performance_attestation_spec.spl:249`,
  `x25519mlkem768_gpu_measurement_qualification_spec.spl:127`
- `expected Indent, found Dedent` — `gpu_build_admission.spl:127`,
  `x25519mlkem768_gpu_build_admission_spec.spl:78`
- `expected identifier, found Newline` — `gpu_lifecycle_snapshot.spl:61`

## Verification notes

- `simple check <file>` exits 0 on the failing file — do not use it as the oracle.
- Reproduce with a driver that imports the module and grep the output for
  `Dedent`; exit status alone is fail-open.
- The fix is in the **Rust seed** parser, which is what currently runs as
  `bin/simple`. The pure-Simple parser does not emit this message and was not
  changed; if it grows the same continuation handling it needs the same
  credit-bounded rule.
