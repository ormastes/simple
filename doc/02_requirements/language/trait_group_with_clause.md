# Feature Request — Trait groups via the existing `with` clause

Status: proposed (2026-08-09)
Design source: `doc/05_design/app/tools/unified_debug_profile_capability_architecture_2026-08-09.md` §3
Plan stream: P0 of `doc/03_plan/agent_tasks/unified_debug_profile_capability_parallel_plan_2026-08-09.md`

## Problem

Composing two orthogonal capability traits (e.g. `DebugTarget` +
`ProfileTarget`) currently requires hand-writing a bundle struct plus a
hand-written acquisition helper. That boilerplate is repeated per pair and
drifts from the member traits.

## Grammar delta — ZERO new tokens

The `with` clause already exists in the lexer (`TokenKind::With`) and is
already parsed on `struct`/`class` headers. This request extends the **trait
header production only**:

```
trait_header := 'trait' IDENT generic_params?
                ( ':' type ('+' type)*        # existing supertrait form
                | 'with' type (',' type)*     # NEW: group form
                )? ':'
```

Example:

```simple
trait DebugProfiler with DebugTarget, ProfileTarget:
    pass_dn
```

No new keyword, no new token kind, no new AST field: group members are
recorded in the **existing** `TraitDef.super_traits`, because
`with A, B` is exactly sugar for `trait G: A + B:`.

## Desugar semantics

1. **Member concatenation.** A group trait desugars to the concatenation of
   its member traits' fn-fields, in member-declaration order, followed by any
   fn-fields the group itself declares.
2. **Blanket satisfaction.** Any type implementing every member trait
   satisfies the group. The group adds no obligations of its own beyond the
   members, so this is sound by construction and reuses the existing
   supertrait rule.
3. **Generated acquisition** `G.from(expr) -> Option<G>`. For each member
   trait `M`, the source expression must expose an accessor whose return type
   is `Option<M>`. `.from()` returns `Some(group)` only when **every** member
   accessor yields `Some`; otherwise `None`.
4. **Missing accessor is a compile error**, naming the member trait and the
   accessor that was not found. `.from()` is not generated in that case, so
   the mistake surfaces at build time, not at run time.

## Acceptance criteria

- AC1: `trait G with A, B:` parses. Previously it failed with
  `Unexpected token: expected Colon, found With`.
- AC2: No new token kinds are introduced; the existing parser corpus is
  unchanged and green.
- AC3: The desugared group carries the union of member fn-fields.
- AC4: A type implementing all members is accepted where the group is
  expected (blanket satisfaction).
- AC5: `G.from(x)` yields `Some` when all member accessors return `Some`, and
  `None` when any returns `None`.
- AC6: A group whose member has no `Option<M>` accessor on the source type
  produces a compile error naming that member/accessor.
- AC7: The existing `trait G: A + B:` supertrait form keeps working
  unchanged.

## Non-goals

- No `+` separator in the `with` clause (comma only, matching struct/class).
- No change to `struct`/`class` `with` semantics.
- Converting existing hand-written group structs to this sugar is follow-up
  work, not part of this request.
