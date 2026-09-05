# Nested immutable combinator placeholder widens to the outer call

Date: 2026-08-22
Status: fixed

## Reproducer

`test/01_unit/lib/nogc_sync_immut/native_combinators_spec.spl` expected
`pfilter([5, 6, 7, 8], _1 > 6)` to return `[7, 8]`, but the Rust bootstrap
seed's interpreter returned `<lambda>`. A named predicate and an explicit
lambda both passed, proving the combinator and callback invocation were sound.

## Root cause

The Rust parser defers placeholder transformation in nested ordinary calls via
`call_arg_depth`. Its higher-order-callee classifier knew collection methods
such as `filter`, but not immutable free-function combinators such as `pfilter`,
`pmap`, and `pfold`. Thus `expect(pfilter(xs, _1 > 6))` left `_1` in the inner
call, and the outer argument transform promoted the entire `pfilter(...)` call
into a lambda. The Pure-Simple transform already gives each call argument its
own boundary and required no change.

## Fix

The Rust postfix parser now maps each supported higher-order API shape and
exact arity to its callback argument position. Free `each(s, f)` uses slot 1,
free ECS `for_each(store, alloc, body)` uses slot 2, while method `each` and
`for_each` use slot 0. Only that argument is force-transformed; collection
data, fold initial values, identifiers, fields, paths, and f-strings retain
their original expression shapes. There is no suffix match and no all-argument
rewrite. Parser coverage checks nested `pmap`, `pfilter`, and two-argument
`pfold` placeholders plus ordinary-call and non-callback negatives. Facade
coverage keeps the exact no-GC sync reproducer and an adjacent GC sync case.

## Build and tree provenance

- Worktree: `/mnt/data/worktrees/simple-full-goal`
- Pre-fix diagnostic seed:
  `/mnt/data/worktrees/simple-main/src/compiler_rust/target/release/simple`
- Pre-fix SHA-256:
  `022dc1df80c3afdafcd78119f71eb23dabb0c9598951f03669c4c129baa78f7c`
- The focused `simple-parser` callback tests pass 3/3 against this checkout.
- Post-fix isolated release seed:
  `/tmp/cargo-target-combinator-release/release/simple`
- Post-fix SHA-256:
  `c2604629cf175d389c0696590f2bac82784753466daa8e24c3fa6cc3791e6d62`
- The exact no-GC sync facade spec passes 1/1, including placeholder `pfilter`
  and two-parameter placeholder `pfold`; the adjacent named/explicit/
  placeholder contract passes 3/3.
