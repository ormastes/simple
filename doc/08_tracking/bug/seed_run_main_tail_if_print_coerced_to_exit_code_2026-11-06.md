# seed_run_main_tail_if_print_coerced_to_exit_code_2026-11-06

- Severity: P2
- Component: Rust seed parser (`src/compiler_rust/parser/src/stmt_parsing/control_flow.rs`)
- Status: fix-implemented-verification-pending (needs a seed redeploy to verify `bin/simple.exe run`)

## Symptom

```
fn main():
    val c = 1 < 2
    if c: print "a" else: print "b"
```

`bin/simple.exe run x.spl` prints `a`, then exits 1 with
`error: semantic: type mismatch: cannot convert string to int`. With `c` false
nothing is printed and it fails the same way. The JIT also reports
`GlobalLoad: unresolved identifier 'print'`.

## Root cause

It looked like main's tail value being coerced to the exit code, but the cause is
in the parser. In the statement-form inline `if` (`parse_if`, inline-expression
arm), the then-branch goes through `parse_expression_or_assignment`, which
handles no-paren calls. The `else:` branch went through plain
`parse_expression()` (control_flow.rs:371). That parsed `print` as a bare
identifier, so the `if` ended there and `"b"` was left over as a separate
statement. That string became main's last statement, and so main's value, and
run's int exit-code conversion then failed on it.

Paren calls (`print("b")`), block forms and `match` arms with no-paren calls
were not affected.

## Fix

The else-branch expression goes through `parse_with_no_paren_calls`, the same
way the then-branch does. With that change a print/unit tail produces nil, and
the exit code is 0.

## Tests

`src/compiler_rust/parser/tests/inline_if_no_paren_else.rs`:
- repro: the tail inline if/else with no-paren `print` is one statement, and both arms are `Call`
- prevention: a non-tail inline if (the next statement is kept), an inline if nested in a block if, a unit fn call tail and a paren tail, an `-> i64` main whose int tail stays `Integer`, a bare text tail that stays strings, and a match tail with no-paren print arms

## Verify after seed redeploy

`bin/simple.exe run` on the snippet above must print `a` and exit 0, and
with `c = 1 > 2` it must print `b` and exit 0.
