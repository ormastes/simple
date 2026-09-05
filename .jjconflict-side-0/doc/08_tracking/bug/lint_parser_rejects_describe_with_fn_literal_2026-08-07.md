# Lint's parser rejects `describe "...", fn():` that the test runner accepts

- **Filed:** 2026-08-07
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Severity:** low — a valid spec form is unlintable; every AST lint is silently skipped for the file
- **Found via:** WP-4 of `doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md`

## Symptom

A spec written with the explicit closure form

```simple
describe "some group", fn():
    it "does a thing":
        expect(1).to_equal(1)
```

runs correctly under `bin/simple test` (examples execute, assertions are
observed), but `bin/simple lint <that file>` fails:

```
<file>:24:61: error[PARSE001]: NOT LINTED: source did not parse - every AST-based
lint was skipped for this file (unexpected token in expression: , ',')
NOT LINTED: 1 file(s) could not be parsed and were never analysed
Lint failed in 1 file(s)
```

Column 61 is the `,` before `fn():`.

## Why it matters

`PARSE001` is fail-**open** in the worst way: the file is reported as an error
but *no* AST lint ever ran on it, so any real diagnostic in that file is
invisible. A spec author who uses the closure form loses all AST lint coverage
and only learns about it from the exit code.

## Workaround used in WP-4

Rewrote the spec to the block form, which both engines accept:

```simple
describe "some group":
    it "does a thing":
```

Recorded here rather than silently normalized, per `CLAUDE.md` ("when a short,
safe grammar form fails … fix it or record a concrete bug/feature request").

## Unblock condition

Either the lint front-end's expression parser accepts a trailing `fn()` literal
argument in a `describe`/`context` call, or the closure form is removed from the
spec DSL and the runner rejects it too. Today the two disagree, which is the
actual defect.

## Reproduce

```bash
printf 'describe "g", fn():\n    it "x":\n        expect(1).to_equal(1)\n' > /tmp/d.spl
bin/simple lint /tmp/d.spl   # error[PARSE001]
```

## Fix

**Root cause:** The pure-Simple frontend's `try_parse_bare_ident_string_call()`
function in `src/compiler/10.frontend/core/parser_stmts.spl:217-229` parsed the
string argument only and returned, leaving comma-separated arguments unparsed.
For `describe "g", fn():`, it created a call with just the string, and the
trailing `, fn():` was rejected during statement parsing.

**Solution:** Extended the function to loop over `TOK_COMMA` tokens after the
string argument, parsing and collecting additional arguments. The loop at
lines 232-235 calls `parse_expr()` for each comma-separated argument, which
correctly handles lambda expressions with indented block bodies (verified in
`parse_fn_lambda_after_kw()` at lines 123-145).

**Commit:** Included in fix for parser-stmts.spl

**Defect 2 (fail-open PARSE001) note:** The silent-skip path was already
fail-closed as of 2026-08-01 (see `entry_and_fixes.spl` lines 87-89, which emit
a reported PARSE001 diagnostic and return early). The file still shows "NOT
LINTED" in the banner and the linter exit code is 3 (distinct from parse-error
exit code 1), ensuring the parse failure is visible. No change required.
