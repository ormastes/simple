# `simple lint` dies on any `pub fn` returning a struct (2026-10-03)

**Status:** open. Found on the Windows phase-1 seed built from `88ecaa21054`.

## Repro

```simple
struct P:
    x: i64

pub fn a(n: i64) -> P:
    P(x: n)
```

`simple lint p3.spl` -> `error: semantic: cannot iterate over this type: Nil`
(rc=1). Without `pub` the same file lints clean; `pub fn` returning `i64`
lints clean.

## Impact
Every file that declares (or transitively imports a module that declares) a
public function returning a struct cannot be linted: on origin `main`,
`src/app/llm_caret/cs_main.spl` and `src/os/apps/smux/smux_remote.spl` both fail
this way, and so do `src/os/apps/smux/api.spl` and `vt_screen.spl`. The lint
verdict for those files is therefore "not evaluated", not "clean".

## Next step
Find the rule that walks a public signature's return type (it gets `nil` for a
user struct's field list) in `src/compiler/90.tools/lint/` or the lint
entry's public-API pass, and make it handle a struct return type.
