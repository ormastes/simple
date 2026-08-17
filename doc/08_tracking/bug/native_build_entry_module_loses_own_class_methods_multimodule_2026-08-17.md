# native-build: an entry module with any `use` import loses its OWN class methods

- **Filed:** 2026-08-17
- **Severity:** P1 — this is not a trailing-defaults edge case. It is a general
  break of concrete-class instance-method dispatch for every multi-module
  `native-build`, i.e. for essentially every real program.
- **Status:** OPEN, diagnosed and bisected, unfixed

## Symptom

```
MIR lowering error: unresolved method call: bump
```

`bump` is an ordinary instance method, defined in the very module being compiled.

## Bisect result — the actual trigger

Reduced from `test/fixtures/native_trailing_default_param/main.spl`. The failing
condition is far more general than the fixture it was found in:

> **Any concrete-class instance-method call, in an entry module that has at least
> one `use` import, under multi-module `native-build`.**

Falsifying controls, all measured:

| shape | result |
|---|---|
| entry module with a `use` import, `w.bump(1)` | **FAIL** — unresolved method call |
| same call, entry module with NO `use` import | PASS |
| trailing default args removed entirely | still FAIL |
| all args supplied explicitly | still FAIL |
| `static fn` on the same class (`Widget.stat`) | resolves (`found=true`) |

So trailing defaults are **irrelevant** — they were a red herring from the
fixture's name. What matters is the presence of a cross-module import at all.

The probe trail shows the entry module's own methods failing static lookup and
falling through to the unresolved arm:

```
[mir-method-call] resolution-arm=unresolved method=bump
[mir-method-call] unresolved-static method=bump srn='' disc=1337030607 found=false
[mir-method-call] unresolved-static method=stat srn='' disc=1337030607 found=true
```

## Locus

`src/compiler/35.semantics/resolve_strategies.spl:133-138` and the symbol-table
population feeding it. When the multi-module closure is built, the entry module's
own class methods are not present in the table it consults — the module loses its
own members in the closure that was supposed to *add* to them.

## Two prior misdiagnoses, both refuted with evidence

This defect cost four-plus rounds across several lanes. Recording the refutations
so nobody re-walks them:

1. **"`undefined variable Widget` in native-build MIR lowering."** REFUTED —
   `grep -n Widget` over the full 2153-line native-build log returns **zero**
   hits.
2. **"`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:49`, a module-level
   `var` with an initializer that native-build's pure-Simple parser rejects
   (`expected Fn, found Assign`) while the Rust seed accepts it."** REFUTED — that
   text appears nowhere in the log. It had already been refuted once by ablation
   in another lane.

## A second, independent defect found alongside it

The real error was invisible for days because the build driver **swallows it**:
`build_outcome.spl` never prints a unit's `diagnostics` field. The outcome summary
reports `ERROR=1` and names the failing unit, and stops there:

```
===== build outcome summary =====
OK=1
ERROR=1
ERROR: 1 unit(s)
  - test.fixtures.native_trailing_default_param.main
===== end build outcome summary =====
```

A build driver that knows why a unit failed and does not say is how a
one-line diagnosis became a multi-lane investigation. Worth its own fix
regardless of this bug.

## OPEN QUESTION — possible shared root with the stage-3 blocker, UNPROVEN

`doc/08_tracking/bug/stage3_post_parse_surface_window_has_no_receipts_2026-08-17.md`
describes a stage-3 failure at `phase=hir` in which symbol lookups resolve to
**foreign** symbols. "A module loses its own members in a multi-module closure" is
the same *family* of complaint, one phase earlier in the pipeline.

**This is explicitly NOT an assertion that they are the same bug.** No shared
root cause has been demonstrated, and the two could easily be independent defects
in different tables. It is recorded because whoever fixes either one should read
the other first: if the symbol-table construction for the multi-module closure is
the common ancestor, one fix closes both, and if it is not, ruling that out is
cheap and worth writing down.

## Guard

`scripts/check/check-native-trailing-default-param.shs` fails on this. Its name
now under-describes what it catches — it is, in effect, the repo's only gate on
multi-module `native-build` instance-method dispatch. Consider renaming it when
this is fixed, and note that the guard is only meaningful where `bin/simple`
exists; see
`doc/08_tracking/bug/guard_silent_nonzero_exit_no_verdict_line_2026-08-17.md`.
