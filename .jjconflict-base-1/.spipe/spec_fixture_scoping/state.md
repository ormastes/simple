# Feature: sspec describe-level fixture scoping

## Raw Request
Lane BRORIGIN reported that `val` fixtures declared at `describe` level are not reliably visible
inside `it` bodies (10 `variable not found` failures across 122 browser-security examples), and
had to move every fixture to module-level functions. Lane ECS3 hit a related shape. Fix it in the
spec library if it belongs there; otherwise file a precise bug.

## Task Type
bug (diagnosis)

## Verdict
**Not a spec-library defect. Compiler defect. Bug filed, no code changed.**

## Root Cause
Closure **selective capture** copies only the identifiers a free-variable walker finds in the
lambda body. The walker descends into expressions correctly, but at a *statement block* it only
recurses into `Node::Expression`. `Node::Let`, `Node::Assignment`, `Node::If`, `Node::For`,
`Node::While`, `Node::Match`, `Node::Return` are skipped, so a describe-level fixture referenced
only from one of those forms is never captured and is absent at runtime.

Twin sites (both in the Rust seed):
- `src/compiler_rust/compiler/src/interpreter/expr/control.rs:36-46` (filter) and `:401-407`
  (block walker); `:389-400` has the same hole for `Expr::Match` arm bodies.
- `src/compiler_rust/compiler/src/hir/lower/expr/control.rs:87-99` (filter) and `~:1172`
  (`collect_identifiers_recursive` block arm).

`capture_all == true` bypasses the filter entirely, which is why the bug appears intermittent.

## Why no library fix
`src/lib/nogc_sync_mut/spec.spl:66` (`describe`) and `:118` (`it`) only call `block()`. The
closure and its captured env are built by the compiler before the library is reached, so the
library has no way to widen the capture.

## Evidence
Binary: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`, the **Rust bootstrap seed**
(emits the "bootstrap seed only" banner). Both engines A/B'd on that same binary
(`SIMPLE_EXECUTION_MODE=interpreter` for the second column) — identical on the sspec matrix,
divergent on plain closures.

Full truth table + the plain-closure silent-`0` finding:
`doc/08_tracking/bug/closure_selective_capture_skips_non_expression_statements_2026-07-27.md`

Headline: inside an `it`, `expect(fx)` and `print "{fx}"` PASS; `val a = fx`, `a = fx`,
`if fx > 5:`, `if true: … fx`, `for …: … fx`, and `val f = fn(): fx` all FAIL with
`semantic: variable \`fx\` not found`. Order-dependent: a prior plain-expression read of `fx` in
the same `it` "rescues" a later `val a = fx`.

Worse outside sspec: the same shapes on a plain `fn()` closure return **`0`** silently under the
JIT (including the direct read), while the interpreter errors. That is a vacuous-assertion hazard.

## Workaround for other lanes (verified on both engines)
Keep fixtures at `describe` level; make the first statement of the `it` a bare-identifier "touch"
of each fixture (`fx` on its own line, or `[fx, cfg]` for several). A bare identifier is a
`Node::Expression`, so the walker captures the name and all later `val`/`if`/`for`/assignment uses
resolve. `build/fixture_scope/w_workaround.spl` — 2/2 pass, JIT and interpreter. Strictly cheaper
than hoisting fixtures to module-level functions, and becomes a no-op after the compiler fix.

## Repros (uncommitted)
`build/fixture_scope/` — `h_matrix.spl` (truth table), `h2_same_it.spl` (order-dependence),
`k2_plain.spl` (plain-closure silent zero), `f1..f6` + `g1..g6` (passing shapes, first repros).

## Blast Radius
`grep -rlP '^ {4}(val|var) \w' --include=*_spec.spl test/` -> **4,525 / 23,894** spec files declare
a describe-level fixture. Affected only where such a fixture is read from a `val`/`var`
initializer, an assignment, or an `if`/`for`/`match`/nested-lambda inside an `it`, with no earlier
plain-expression reference in the same `it`. Loud failure inside sspec (red example, not a false
green); silent inside ordinary code.

## Next Step (owner: a compiler lane, not FIXTURE)
Recurse into all statement forms in both block walkers. Over-capture is harmless — the filter is
an optimisation. Separately fix the JIT's `0` substitution for a missing capture.

## Not Done
No regression spec added: the behavior is not fixed, and a spec asserting the correct behavior
would be red. Add one together with the compiler fix.
