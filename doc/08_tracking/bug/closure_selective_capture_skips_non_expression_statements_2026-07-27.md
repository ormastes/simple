# Closure selective-capture walks only `Node::Expression` statements — outer locals vanish inside `val`/`if`/`for`/assignment

- **Filed:** 2026-07-27 (lane FIXTURE)
- **Severity:** High — silently loses values (JIT) or hard-errors (interpreter); the primary
  symptom is "sspec `describe`-level fixtures are not visible inside `it`", which pushes every
  spec author to module-level state.
- **Component:** compiler — closure free-variable analysis. **NOT** the spec library.
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  descend into every statement form and into match arms, with sequential shadowing. Regression
  spec: `test/01_unit/compiler/closure_capture_statements_spec.spl` (30 examples; 22 of them fail
  on the pre-fix binary, 0 after). See "Fix" below. Not yet ported to the pure-Simple
  `src/compiler` tree — see "Remaining".

## Fix (2026-07-27, lane CAPFIX)

Both free-variable walkers were rewritten as proper scope-aware walkers:

- `src/compiler_rust/compiler/src/interpreter/expr/control.rs` — `collect_free_vars`
- `src/compiler_rust/compiler/src/hir/lower/expr/control.rs` — `collect_used_identifiers`

Each now has a statement walker (`Node::Let`/`Const`/`Static`/`Assignment`/`Return`/`If` incl.
`elif`/`else`/`if let`, `Match`, `For`, `While` incl. `while let`, `Loop`, `Break`, `Defer`,
`ErrDefer`, `Guard`, `Assert`/`Assume`/`Admit`, `Calc`, `Context`, `With`, nested `Function`)
plus a block walker that treats a statement list as a lexical scope, and match arms are walked
through their bodies rather than only their `Node::Expression` statements. The expression walker
also gained the arms it silently dropped (`Range`, `Await`, `Try`, `ForceUnwrap`, `ExistsCheck`,
`Unwrap*`/`Cast*`/`Coalesce`, `OptionalChain`/`OptionalMethodCall`, `Slice`, `Dict`,
comprehensions, `Spread`, `ArrayRepeat`, `LabeledTuple`, `TupleIndex`, `StructInit` spread,
`Go`, `KernelLaunch`, `Forall`/`Exists`) — and, in the HIR/JIT twin, an `Expr::DoBlock` arm,
which did not exist at all: that is why a `fn(): ...` block body captured *nothing* under the
JIT, including the direct read (row KA).

Shadowing is honoured **sequentially**: a `val`/`var`, `for` binder, `if let`/`while let`
pattern, match-arm pattern, `with ... as` name, or nested lambda parameter removes the name from
the free set for the statements it covers, but a binder's own initializer is walked *before* the
binder exists, so `val fx = fx + 1` still captures the outer `fx`. Bindings introduced inside a
nested block are dropped at the end of that block, so a later read is captured again (an
over-capture, which is the safe direction — the filter is only an optimisation).

### Verified truth table (both engines, fixed binary)

`h_matrix.spl` H1-H10, `h2_same_it.spl` P1/P3/P4/P5, and `k2_plain.spl` KA-KF: every row that
failed above now passes, and every previously passing row still passes. `k2_plain` prints
`KA_DIRECT=10 KB_LET=10 KC_LETADD=11 KD_ASSIGN=10 KE_FOR=10 KF_IF=10` under both the JIT and the
interpreter — the silent-`0` substitution is gone.

### Remaining

- The pure-Simple self-hosted compiler (`src/compiler`) has not been checked for the same hole;
  lanes were live there and it is out of this lane's scope.
- Separate, pre-existing, NOT a capture defect: block-local binder lifetime. `val fx = 55` inside
  an `if` body and a `for fx in ...` binder both leak into the enclosing scope, identically inside
  and outside closures, and the JIT and interpreter disagree about the `if` case (55 vs 10;
  probe `build/capfix/scope_probe.spl`, same result on the pre-fix binary). The regression spec
  deliberately does not pin that behaviour.

## Summary

Lambda/block closures use **selective capture**: only the identifiers the analysis believes the
body references are copied into the captured environment. The free-variable walker recurses
through *expressions* fine, but when it reaches a **block of statements** it only descends into
`Node::Expression` statements. `Node::Let`, `Node::Assignment`, `Node::If`, `Node::For`,
`Node::While`, `Node::Match`, `Node::Return` are all skipped, so any outer variable referenced
*only* from one of those statement forms is never captured.

At runtime the name is then simply absent from the closure env.

## Root cause (file:line)

Interpreter path — `src/compiler_rust/compiler/src/interpreter/expr/control.rs`:

- **:36-46** — `Expr::Lambda` with `capture_all == false` filters the env by
  `collect_free_vars(body)`.
- **:401-407** — the block arm of the walker:

```rust
Expr::DoBlock(nodes) | Expr::UnsafeBlock(nodes) => {
    for stmt in nodes {
        if let Node::Expression(e) = stmt {   // <-- only Node::Expression
            collect_free_vars_recursive(e, vars);
        }
    }
}
```

- **:389-400** — `Expr::Match` arm bodies have the identical `if let Node::Expression(e)` hole.

JIT / HIR path — `src/compiler_rust/compiler/src/hir/lower/expr/control.rs`:

- **:87-99** — `lower_lambda` filters `ctx.locals` by `collect_used_identifiers(body)`.
- **~:1172** — `collect_identifiers_recursive` has the same `Node::Expression`-only block arm.

Twin defect, two trees. `capture_all == true` (set for some lambda forms, see
`hir/lower/expr/control.rs:227` `let capture_all = !has_args;`) takes the unfiltered path and is
unaffected — which is why the bug looks intermittent.

## Not a spec-library bug

`src/lib/nogc_sync_mut/spec.spl` `describe`/`it` (lines 66 / 118) do nothing but `block()`.
The closure and its captured env are already built by the compiler before the library sees them,
so the library cannot widen the capture. No library-side fix exists.

## Visibility truth table

Binary: `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`, the **Rust bootstrap seed**
(prints the "bootstrap seed only" banner). Both columns are that same binary; `interp` =
`SIMPLE_EXECUTION_MODE=interpreter`.

Repro: `build/fixture_scope/h_matrix.spl` — `describe` with `val fx = 10`, one `it` per row.

| # | Shape inside the `it` body | Statement node | default (JIT) | interp |
|---|---|---|---|---|
| H1 | `expect(fx).to_equal(10)` | `Node::Expression` | PASS | PASS |
| H2 | `print "H2={fx}"` | `Node::Expression` | PASS | PASS |
| H3 | `val a = fx` (first stmt) | `Node::Let` | **FAIL** `variable \`fx\` not found` | **FAIL** |
| H4 | `val a = 1` then `expect(fx)…` | Let(no fx) + Expr | PASS | PASS |
| H5 | `expect(fx)…` then `val a = 1` | Expr + Let(no fx) | PASS | PASS |
| H6 | `if fx > 5:` (stmt condition) | `Node::If` | **FAIL** | **FAIL** |
| H7 | `if true:` / body reads `fx` | `Node::If` | **FAIL** | **FAIL** |
| H8 | `for i in [1]:` / body reads `fx` | `Node::For` | **FAIL** | **FAIL** |
| H9 | `val f = fn() -> i64: fx` | `Node::Let` | **FAIL** | **FAIL** |
| H10 | two direct `expect(fx)` stmts | `Node::Expression` | PASS | PASS |

Order-dependence (`build/fixture_scope/h2_same_it.spl`) — the smoking gun:

| # | Shape | Result |
|---|---|---|
| P1 | `expect(fx)…` **then** `val a = fx` | PASS — the earlier `Node::Expression` read got `fx` captured, so the later `Node::Let` finds it |
| P3 | `val a = fx + 0` (first stmt) | **FAIL** |
| P4 | `var a = 0` then `a = fx` | **FAIL** (`Node::Assignment`) |
| P5 | `expect(fx + 1).to_equal(11)` | PASS |

Also passing (do **not** regress these): describe-level `var` read directly; fixtures in nested
`describe` up to 4 levels; fixture read in the `describe` body itself; text / array / struct
fixtures; fixtures produced by a function call — see `build/fixture_scope/f*.spl`,
`g2_fn_call_fixture.spl`, `g3_deep_nest.spl`.

## Worse: silent zero outside sspec (not just an error)

The same defect on a plain (non-BDD) closure does **not** error under the JIT — it yields `0`.
`build/fixture_scope/k2_plain.spl`, `fn outer()` with `val fx = 10` passing `fn()` blocks to
`fn runner(block: fn())`:

| row | body | default (JIT) | interp |
|---|---|---|---|
| KA | `print "KA_DIRECT={fx}"` | `0` **(silently wrong)** | `10` (correct) |
| KB | `val a = fx` | `0` | error `variable \`fx\` not found` |
| KC | `val a = fx + 1` | `1` **(silently wrong)** | — |
| KD | `var a = 0; a = fx` | `0` | — |
| KE | `for i in [1]: print fx` | `0` | — |
| KF | `if true: print fx` | `0` | — |

Two things here: (a) the JIT loses even the *direct* read for a lambda passed as a `fn()`
parameter, and (b) it substitutes `0` rather than failing. An assertion written this way passes
vacuously. This is the "assertion that never runs" hazard.

## Suggested fix

Make both block walkers recurse into every statement form, not just `Node::Expression`:
`Node::Let` (initializer), `Node::Assignment` (target + value), `Node::If` (condition + both
branches), `Node::For` (iterable + body), `Node::While`, `Node::Loop`, `Node::Match`,
`Node::Return`, `Node::With`. Over-capturing is harmless here (the filter is an optimisation);
under-capturing is a correctness bug. The `Expr::Match` arm-body walker needs the same treatment.

Separately, the JIT's lost direct read (KA above) and its `0` substitution should be fixed or
turned into a hard error — a missing capture must never silently become `0`.

## Workaround (verified, both engines)

Keep fixtures at `describe` level; add a **bare-identifier "touch" statement** as the first line of
the `it`. A bare `fx` is a `Node::Expression`, so the walker sees it and captures the name; every
later `val`/`if`/`for`/assignment use then resolves. `build/fixture_scope/w_workaround.spl`:

```
it "…":
    fx          # touch — forces capture
    cfg
    val a = fx
    if a > 5:
        expect(a).to_equal(10)
```

A list literal touches several at once: `[fx, cfg]`. This is strictly better than hoisting every
fixture to a module-level function, and it reverts to a no-op once the compiler fix lands.

## Repros

All under `build/fixture_scope/` (not committed):
`h_matrix.spl` (truth table), `h2_same_it.spl` (order-dependence), `k2_plain.spl` (plain-closure
silent zero), `f1..f6` / `g1..g6` (passing shapes + first reproductions).

## Blast radius

`grep -rlP '^ {4}(val|var) \w' --include=*_spec.spl test/` → **4,525 of 23,894** spec files
declare a fixture at describe level. Each is affected *only* if that fixture is read from a
`val`/`var` initializer, an assignment, or an `if`/`for`/`match`/nested-lambda inside an `it`,
and only when no earlier plain-expression statement in the same `it` already referenced it.
The failure is loud (`variable X not found`) inside sspec, so it surfaces as a red example
rather than a false green — but the same defect in non-spec code is silent.

## Evidence 2026-08-17 (fleet worker A, rust-seed slice)

Content check of `src/compiler_rust/compiler/src/hir/lower/expr/control.rs`:
lines 2424-2429 carry the landed capture-walker fix and name this very file:

> "...and had no `Expr::DoBlock` arm at all, so a `fn(): ...` block body captured
>  ... doc/08_tracking/bug/closure_selective_capture_skips_non_expression_statements_2026-07-27.md"

So the **walker half is confirmed fixed in current source**. The half this doc
leaves open — the JIT substituting `0` for the closure's lost direct read — is
NOT in `control.rs`; it is a cranelift codegen concern and was not located or
verified here.

**Verdict: STILL-OPEN (JIT half only). Walker half ALREADY-FIXED by content.**
**Not proven:** the JIT half. A JIT defect cannot go red from a spec body
(spec bodies run interpreted) and the subprocess comparison could not be run —
see "Execution blocked" below.
