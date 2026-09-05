# Grammar: trait-header `with` clause (capability groups)

**Status: PARSER LANDED, DESUGAR LANDED, FEATURE INERT.**
Nothing can use this syntax today. See "Reachability" below before planning
work against it.

Origin: `doc/05_design/app/tools/unified_debug_profile_capability_architecture_2026-08-09.md` §3
(read its CORRECTION block — it overrides the prose beneath it).
Implemented by stream P0 (`50f06dcdd56`), corrected by P0b (`8477ff5bdd0`).

## Requirement

A *capability group* is one trait that is the literal union of its member
traits' method sets. Express it by extending the **existing** `with` clause —
already parsed on `struct X with Mixin:` — to the trait-header production.

- No new keyword.
- No new token (specifically: not `+`).
- A pure group adds zero methods of its own.

```simple
trait DebugProfiler with DebugTarget, ProfileTarget:
    pass
```

Desugars to the concatenation of the members' fn-fields, exactly as if the
group had been written longhand.

## Non-requirements / explicitly rejected

- **`.from()` pairing acquisition is rejected as UNSOUND.** The original design
  specified a generated `Group.from(a, b)`. Classes are value types, so pairing
  `session.debug()` with `session.profile()` yields two diverging copies —
  measured RED by P2 (8/70, `expected 6, got 0`). A group must be acquired
  through a **single** accessor over a **single** value. Writeup:
  `doc/08_tracking/bug/capability_group_from_unsound_under_value_semantics_2026-08-09.md`.
- The group does not introduce accessors. Accessors live on the core trait.

## Constraints the grammar cannot enforce (but implementers must)

- Every mutating method is `me`; a `fn` trait method receives a copy and
  silently discards mutation.
- A capability handle stops aliasing unless acquired as a function's **tail**
  expression
  (`doc/08_tracking/bug/ref_debug_profiler_handle_stops_aliasing_unless_tail_expression_2026-08-09.md`).

## Reachability — why this is inert

1. `desugar_traits` (`src/app/desugar/trait_desugar.spl`) is a **text-level,
   pre-parse** transform. Its sole caller is `src/app/desugar/mod.spl:210` in
   the standalone `app.desugar` tool. The compiler deliberately does not import
   `app.desugar` (`src/compiler/20.hir/hir_forward_lowering.spl:33-35`), so no
   ordinary compilation runs it.
2. The **deployed seed predates the parser change**.

## Remaining work to make it real

- Wire trait-group flattening into the compiler's own trait path
  (`trait_scanner.spl` / `forwarding.spl` in `25.traits`), not the text-level
  desugar tool — or accept the text tool and give it a compile-path caller.
- Re-bootstrap so the deployed compiler accepts the header form.
- Add a spec that **compiles and executes** a group-using program. P0's
  generator specs passed 21/21 while emitting code that could not compile;
  text/structure assertions are not adequate here.

## Current workaround (in production use)

Write the group longhand — a trait listing every method of both members — and
supply one `<backend>_debug_profiler(session)` accessor per backend. Landed:
`src/lib/common/debug/debug_profiler.spl`.
