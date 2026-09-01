# `if val` expression form loses the bound pattern variable

**Status:** Open  **Found:** 2026-07-20 (whole-suite triage cluster, test/03_system/)
**Affected spec:** `test/03_system/interpreter/interpreter_regression_spec.spl`
  — `describe "Bug 1d - plain if-val unwraps Option"`,
  `it "expression form selects by presence and binds the payload"` (line 182)

## Symptom

The **statement form** of `if val` (bind, then use the variable in following
statements) works correctly — see the sibling example in the same
`describe` block, `it "statement form skips None and binds the Some payload"`
(line 171), which passes.

The **expression form** — `if val <pat> = <expr>: <then-expr> else:
<else-expr>` used as a value — loses/misresolves the bound pattern variable
inside the `then` branch:

```simple
fn optional_number(present: bool) -> i64?:
    if present:
        return Some(7)
    None

fn main():
    val present = if val value = optional_number(true): value else: -1
    print(present)
```

- Under `bin/simple run`: prints `<enum@0x...>` instead of `7` — the
  expression evaluates to the raw `Option`/enum value itself rather than
  the unwrapped payload bound by `value`.
- Under `bin/simple test` (SSpec evaluator): fails semantic analysis outright:
  `semantic: variable \`value\` not found`.

Minimal spec repro (reproduces the `test`-path symptom directly):

```simple
use std.spec.describe
use std.spec.it
use std.spec.expect

fn optional_number(present: bool) -> i64?:
    if present:
        return Some(7)
    None

describe "if-val expression form repro":
    it "binds payload in then-branch":
        val present = if val value = optional_number(true): value else: -1
        expect(present).to_equal(7)
```

Command: `SIMPLE_RUST_SEED_WARNING=0 timeout 60 bin/release/x86_64-unknown-linux-gnu/simple test <repro>.spl --no-session-daemon`

Result: `✗ binds payload in then-branch` / `semantic: variable \`value\` not found`.

## Relationship to existing bug docs

Distinct from `interpreter_if_val_nil_mismatch_option_2026-07-03.md`, which is
about the **statement form** wrongly taking the true branch on a genuinely
`nil` Option (a false-positive match). This bug is about the **expression
form** specifically: the pattern variable bound by `if val` is not correctly
threaded into the `then`-branch expression's scope/value — it fails semantic
resolution under `test` and returns the un-unwrapped enum under `run`. Two
different facets of the same broader "`if val` expression form is unreliable"
feature gap — file separately since the concrete defect and repro differ.

## Root-cause hypothesis

The statement-form `if val` binds `value` as a local in the block scope of
the `then` branch's *statement list*. The expression-form variant likely
lowers/evaluates the `then`/`else` arms as bare expressions without wiring
the pattern-bound variable into their evaluation environment/scope — under
`test`'s semantic-analysis pass this shows up as an unresolved-variable
error; under `run`'s (looser) interpreter path it falls through to returning
the outer `if val`'s subject value unchanged (the raw enum) instead of the
unwrapped binding.

## Impact

Any code using `if val` as a value-producing expression (not just a
statement) with the bound variable used in the `then` arm is affected. The
guard test `interpreter_regression_spec.spl` (a regression-guard spec, per
its name) currently fails on this exact pattern, meaning this is a
**regression** against previously-verified behavior, not a new/never-worked
feature.
