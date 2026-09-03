# `export use m.f as g` does not bind — no renaming re-export

Filed 2026-09-03. Status: OPEN. Class: language/module-system gap (not a crash).

## Summary

A re-export can rebind a name into another module (`export use m.f`), but it
cannot **rename** while doing so. `export use m.orig as aliased` is accepted by
the parser and then resolves to nothing: the alias is never bound.

## Reproduction (30 seconds, no build)

`m.spl`:
```simple
fn orig(x: i64) -> i64:
    x + 1
export orig
```

`use_alias.spl`:
```simple
export use .m.orig as aliased
fn main() -> i64:
    print str(aliased(1))
    0
```

```
$ src/compiler_rust/target/release/simple run use_alias.spl
error[E1002]: function `aliased` not found
```

Verified twice on 2026-09-03, independently: once by the agent implementing the
sosix facade, once directly. Same error text both times.

## Why this is load-bearing, not cosmetic

The standing architectural directive for tool code is: depend on a **sosix**
facade rather than on native/POSIX libraries directly, and make that facade cost
nothing where it forwards to the same POSIX primitive — "use an alias, so
callers think it is sosix but it directly uses posix".

A plain re-export is exactly that: a name binding, no call frame. But the
facade's names are `sosix_`-prefixed while the underlying primitives are
`process_*` / `which`. Without renaming, **not one** symbol in the facade can
be a true re-export. Every renamed symbol must instead be a forwarding
function.

Measured on the first facade (`src/lib/nogc_async_mut/sosix/host_facade.spl`):
0 of 7 symbols could be re-exports. Four became `@always_inline` single-call
pass-throughs (repo precedent: `process_run_direct`, `process_kill_unchecked`
in `src/lib/nogc_sync_mut/io/process_ops.spl`), which codegen should collapse;
three are genuine adapters that would need a wrapper regardless (a tuple→struct
shape change, a value-domain mapping, and one primitive that does not exist
yet).

So the directive is satisfiable today only via `@always_inline`, which relies on
the inliner rather than on the name resolver. That is a weaker guarantee: it is
a codegen optimisation, not a structural one, and it is not verified anywhere.

## Scope of the cost

Every facade in this repo that renames while forwarding pays one wrapper per
symbol. The `variants/` overlay does not help — it selects a module ROOT, so it
requires the exported names to already match.

## What "fixed" looks like

`export use m.orig as aliased` binds `aliased` in the importing module to the
same symbol as `m.orig`, with no wrapper function emitted, and
`aliased(1) == m.orig(1)`.

## Not claimed here

That the current `@always_inline` pass-throughs are slow. They are very
probably free after inlining; nobody has measured it. The complaint is that the
zero-cost property currently depends on an optimisation rather than on the
module system, and that a facade cannot express its intent directly.

## Related

- `doc/07_guide/language/module_system.md` — E0410 (`pub` alone exports nothing;
  `export use X.*` is needed for shims). Renaming is not covered there.
- `doc/02_requirements/nfr/cs_caret_suite.md` NFR-2 — the requirement this gap
  degrades.
