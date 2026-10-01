# `@cfg(not(...))` rejected by the deployed parser; `match` on imported constants mis-types

- Status: OPEN (2026-09-26)
- Host: this Linux aarch64 box, deployed compiler `bin/simple`
- Found while building the SOSIX interface slice
  (`src/os/services/sosix/`, lane codex/spipe-local-knowledge-setup).

## Symptom 1 — `@cfg(not(...))` parse error

Any `@cfg(not(<arch>))` line fails to parse, for every arch name tried
(`arm64`, `x86_64`), with the error pointing at the closing paren:

```
[parser_error] line 1:16: unexpected token in expression: ) ')'
```

Repro (isolated `bin/simple check`, also hit inside `src/os` files):

```spl
@cfg(not(arm64))
val MACHINE: text = "unknown"
```

`@cfg(arm64)` on the same construct parses and semantically passes.
`src/os/kernel/ipc/syscall.spl` carries `@cfg(not(x86_64))` lines, so the
form presumably worked under a different compiler generation; the deployed
`bin/simple` rejects it. Impact: conditional else-arms must be spelled
unconditionally or with inverted `@cfg(...)` arms, which is not always
expressible.

## Symptom 2 — `match` on imported `val` constants mis-types

```spl
use os.kernel.errno.*          # wildcard import resolves (named import of
                               # non-pub vals separately flakes with
                               # "missing module surface")
fn name(err: i32) -> text:
    match err:
        case EINVAL: "EINVAL"
        case _: "EUNKNOWN"
```

yields `error[semantic]: type mismatch: expected Optional(Infer), found Bool`
at span 0:0 (useless position). Literal arms instead
(`case 22:`) fail with `expected Int(64), found Int(32)` — integer literal
arms are inferred as i64 and do not unify with an i32 subject.

## Workaround in use

The codebase's proven errno-to-text idiom — i64 parameter + if/elif chain
with literal numbers — is unaffected
(`src/lib/common/wine_posix_adapter.spl::wine_posix_adapter_errno_name`,
`src/os/libc/simpleos_string_search.spl::libc_strerror`). New SOSIX modules
(`src/os/services/sosix/errno_text_v1.spl`,
`src/os/services/sosix/interface_v1.spl`) follow it.

## Ask

1. Parser: accept `@cfg(not(<ident>))` (or document the supported grammar
   and grandfather/repair the syscall.spl usages).
2. Match: allow non-pub `val` constants as case patterns and unify integer
   literal arm width with the subject type.
