# `on` is an undocumented reserved word — `val on = ...` fails to parse

- **Filed:** 2026-08-02
- **Status:** OPEN
- **Severity:** low (clear compile error, no silent miscompile) but it costs a
  confusing debug cycle and the message does not name the cause
- **Evidence tier:** Rust seed (`bin/simple`; bootstrap-identity probe = 0)

## Summary

`on` cannot be used as an ordinary identifier. Binding it fails at parse time
with an error that never mentions `on` being reserved:

```
$ cat kw.spl
fn main() -> i64:
    val on = 1
    print "{on}"
    0

$ bin/simple kw.spl
error: compile failed: parse: in "kw.spl": Unexpected token: expected pattern, found On
```

The token name `On` in the diagnostic is the only hint. `off` is fine; only
`on` is affected.

## Why this is filed rather than worked around silently

`on` is not in the reserved-keyword list in `.claude/rules/language.md`
(`gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`, `pass_todo`,
`pass_do_nothing`, `pass_dn`) nor, as far as could be found, in
`doc/07_guide/quick_reference/syntax_quick_reference.md`. It is a natural
variable name for any on/off pair — it was hit while writing
`test/01_unit/lib/mem_infra/harden_backend_parity_spec.spl`, where `val on` /
`val off` held the two halves of a sabotage control. The workaround (rename to
`harden_on` / `harden_off`) is fine locally, but per the repo rule a compact
form that fails should be fixed or recorded rather than quietly normalised.

## Requested resolution, in preference order

1. **Make `on` a soft keyword** — usable as an identifier wherever it is not in
   the position that needs it. This is the behaviour `off` already has, so the
   asymmetry is likely unintentional.
2. If `on` must stay hard-reserved, **say so in the diagnostic** ("`on` is a
   reserved word") and add it to the reserved list in
   `.claude/rules/language.md` and the syntax quick reference.

## Notes

The grammar position that consumes `on` was not identified — it does not appear
as a keyword string in the pure-Simple lexer or in
`src/compiler_rust/compiler/src/lexer/token.rs` under a plain `"on"` match, so
whatever introduces the `On` token is indirect. Finding it is part of the fix.
