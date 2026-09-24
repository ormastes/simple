# `on` is an undocumented reserved word — `val on = ...` fails to parse

## Re-measured 2026-09-13 — still OPEN, but the failure has MOVED

Binary: Rust seed `build/vt4/bootstrap/simple.exe`, `simple run <file>`
(Windows). The reported repro no longer fails the reported way — but `on` is
still unusable, so this entry stays OPEN. Do not close it on the old repro.

What changed: the diagnostic is no longer
`Unexpected token: expected pattern, found On` at the *binding*. `val on = 1`
now binds fine. The parser now dies at the *use* site, claiming `on` starts an
AOP advice declaration:

```
Unexpected token: expected pointcut expression 'pc{...}', found <next token>
```

Measured matrix (each a whole 2-4 line program, top level unless noted):

| program | result |
|---|---|
| `fn main() -> i64:` / `val on = 1` / `print "{on}"` / `0` + `main()` | **prints 1 — works** |
| `val on = 1` / `print on` | FAIL `expected pointcut expression 'pc{...}', found Newline` |
| `var on = 5` / `print on + 1` | FAIL `... found Plus` |
| `var on = 5` / `on = on + 1` / `print on` | FAIL `... found Newline` |
| `fn f(on: i64) -> i64:` / `on + 1` | FAIL `... found Plus` |

So: `on` is accepted as a *binder* (and inside `{...}` string interpolation,
which is lexed separately), and rejected everywhere it is *read*. That is a
worse state than reported, not a better one — the original error at least
pointed at `on`; the new one names `pc{...}`, an AOP construct the user never
wrote, so it is even further from naming the cause.

The requested resolutions below are unchanged and still apply; item 2 (say so
in the diagnostic) is now strictly more urgent.

**Not fixed here:** the parser lives in `src/compiler_rust/**` for this lane,
which was off-limits during this pass (concurrent bootstrap).


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
