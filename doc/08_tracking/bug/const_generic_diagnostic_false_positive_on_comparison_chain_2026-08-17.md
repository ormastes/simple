# Const-generic diagnostic false-positives on a comparison chain, breaking valid stdlib source

Date: 2026-08-17
Status: FIXED (seed-side, verified on a rebuilt seed); pure-Simple parser
mirrored with a narrower fix — see "Parity gap" below.
Area: src/compiler_rust/parser, src/compiler/10.frontend

## Symptom

Valid Simple source failed to parse:

```
fn probe(offset: i32, needle_len: i32, haystack: text) -> bool:
    if offset < 0 or offset + needle_len > (haystack.len() as i32):
        return false
    return true
```

```
error: compile failed: parse: Unexpected token: expected a type in generic
argument position (Simple has no const generic parameters, so a numeric literal
such as `Tensor<i64, 2>` is not a valid generic argument; drop the explicit
generic arguments and let them be inferred, e.g. `Tensor(...)`), found integer literal
```

That line is real stdlib source —
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl:500`
— so the whole browser_engine module became uncompilable. It blocked, with a
parse error and zero examples executed:

- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_engine_vulkan_readback_spec.spl`
  (`declared>=1 executed=0 passed=0 failed=1 reason=parse-error`)
- `bin/simple run src/app/browser/main.spl --sandbox-status` (exit 1)

## Root cause

`try_skip_ident_generic_args`
(`src/compiler_rust/parser/src/expressions/postfix.rs`) decides that a `<`
opened a generic-argument list if the matching `>` is followed by `(`, `.`,
`::` or `{`. That test is far too weak on its own, and nothing else constrained
the list's CONTENTS:

- `parse_type` accepts a bare identifier as a named type, and the keywords in a
  boolean chain lex as identifiers, so `or` and `c` were consumed as "type
  arguments";
- after each argument the loop only *optionally* consumed a `,` and otherwise
  fell through, so a missing separator never aborted the walk.

So `a < 0 or c > (d)` was walked as the argument list `0`, `or`, `c`, reached
the `>` with `(` after it, and was accepted as a confirmed generic-argument
list. Once the 2026-08-17 const-generic work made a numeric literal a recorded
const-argument candidate, that acceptance escalated a silent misparse into a
hard error.

This is therefore two defects in one place:

1. **The regression** — comparison chains containing an integer now fail to
   parse (`a < 0 or c > (d)`).
2. **A pre-existing latent misparse** — comparison chains WITHOUT an integer
   were silently reinterpreted as a generic call. Measured on the pre-fix
   deployed seed, `a < b and c > (d)` gave
   `Unexpected token: expected Colon, found LParen`; it evaluates correctly
   after the fix. This one predates the const-generic work.

The trailing `(` is what arms it, which is why it hid for so long:

| source | pre-fix |
|---|---|
| `a < 0 or b + c > (d as i32)` | const-generic error |
| `a < 0 or c > (d as i32)` | const-generic error |
| `a < 0 and c > (d as i32)` | const-generic error |
| `a < 0 or c > (d)` | const-generic error |
| `a < 1 or c > d` (no paren) | parses fine |

## Fix

Require that each generic argument be followed by an argument separator (`,`)
or a list terminator (`>` / `>>`); otherwise break and let the caller
backtrack into the comparison it actually is. New predicate
`at_generic_arg_separator()`, applied after a const-argument literal and after
a successful `parse_type`.

## Verification (rebuilt seed)

`cargo build --release --bin simple` → `Finished release profile in 3m 12s`,
run as `src/compiler_rust/target/release/simple` (the deployed `bin/simple` was
deliberately NOT overwritten):

```
1. false positive gone
   $ simple run cg_fp.spl
   probe=true                                    (was: const-generic parse error)

2. the intended diagnostic is PRESERVED
   $ simple run cg_real.spl     # val a = Box2<i64, 2>(v: 7)
   Unexpected token: expected a type in generic argument position
   ... no const generic parameters ...

3. ordinary turbofish still works
   $ simple run cg_ok.spl       # val a = Box2<i64, i32>(v: 7)
   ok

4. the latent misparse is also fixed
   $ simple run mis.spl         # if a < b and c > (d):
   old deployed seed: error: ... expected Colon, found LParen
   rebuilt seed:      r=true

5. the blocked lane now runs
   $ simple run src/app/browser/main.spl --sandbox-status
   exit=0, const_generic_errors=0
   browser sandbox: unjailed-in-process — engine and page script run in the
   host process; set SIMPLE_BROWSER_SANDBOX=1 to require the jailed renderer worker
```

## Parity gap (pure-Simple parser)

`src/compiler/10.frontend/core/parser_expr.spl` has the same weak confirmation
and the same unconstrained walk. It was mirrored only where the mirror is
provably safe: the separator requirement is applied **after an integer literal
only**. Unlike the Rust parser — where `parse_type` consumes a complete type —
this one walks a type argument token by token, so requiring `,`/`>` after every
identifier would reject legitimate arguments such as `Foo<T?>`, `Foo<a.b.C>`
and `Foo<T[]>`. That narrower fix removes the regression (defect 1) but NOT the
pre-existing latent misparse (defect 2) on the pure-Simple side.

**The pure-Simple half is UNVERIFIED**: proving it requires a bootstrap, which
was not run in this session. Only the Rust seed fix above is backed by measured
evidence.

## Related

- `doc/08_tracking/bug/const_generic_argument_rejected_in_constructor_call_2026-08-17.md`
  — the change that introduced the regression. Its diagnostic is intentionally
  kept; only the over-broad acceptance is corrected.
