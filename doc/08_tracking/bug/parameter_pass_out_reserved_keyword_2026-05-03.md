# Function parameters named `pass` or `out` silently misbehave

**Status:** OPEN. Reproduced multiple times across the W17–W29 cohort. Severity: silent miscompute.
**Path:** `bug` track. Compiler/parser.

## Symptom

Naming a function parameter `pass` or `out` produces broken behavior at the call site
without a clean parse/lint error:

- W29-G HTTP Digest: `digest_authorize(..., pass: text, ...)` — interpreter resolves the
  parameter as an empty list at every call site (silent empty-payload). Renaming
  to `password` fixed all 31 spec asserts.
- W28-N TLS KeyUpdate: `out` parameter likewise silently corrupted.
- Memory `feedback_simple_parser_strict_callsites.md` already documents that the
  interpreter rejects named-arg fn calls in some shapes; this is a more severe
  variant — the value is not rejected, it is silently wrong.

## Reproduction

```spl
fn auth(user: text, pass: text) -> text:
    pass  # in interpreter mode this evaluates to empty list, NOT the parameter
```

The function body's reference to `pass` is parsed as the `pass_do_nothing` /
`pass_dn` reserved keyword (per `.claude/rules/language.md`), not as a load of
the parameter. Lint/parser produces no error because `pass` is also legal as a
statement.

## Root cause

`pass`, `out`, `gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`,
`pass_todo`, `pass_do_nothing`, `pass_dn` are reserved keywords per
`.claude/rules/language.md`. The parser allows these as parameter NAMES (via the
ident slot in `(param_name: type)`) but resolves bare references inside the
function body as the keyword, not as a parameter load.

## Fix

Either:
1. **Reject reserved keywords as parameter names at parse time** — strictest, but
   churn for any callers using `pass`/`out` today.
2. **Shadowing rule** — when a function parameter binds a name that matches a
   reserved keyword, the body resolves the bare ident as the parameter (shadowing
   semantics). The keyword still works at statement position via context.
3. **Lint warning** that names a problematic parameter and proposes the rename.

Option 1 is cleanest and matches user expectations (Rust/Python both reject
`def fn(pass=...)`).

## Affected sites

Caught at:
- W29-G `src/os/http/auth/digest.spl` (renamed `pass`→`password` — landed)
- W28-N `src/os/tls13/tls13_key_update.spl` (renamed `out`→sibling pattern)
- Memory `feedback_simple_parser_strict_callsites.md`

Likely many more across the codebase. A grep for `fn .*pass\s*:` / `fn .*out\s*:`
would surface candidates.

## Cross-references

- `.claude/rules/language.md` (reserved-keyword list)
- `feedback_simple_parser_strict_callsites.md`
- W29-G commit `5a3f386806` (impl) / `41e347ff8e` (rename fix)
- W28-N commit `46d0efd632`
