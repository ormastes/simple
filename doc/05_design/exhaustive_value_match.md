# Exhaustive value-position `match` (E-MATCH-NONEXHAUSTIVE-VALUE)

Status: ACCEPTED (user decision, 2026-11-02). Lane: exhaustive-value-match.
Closes the silent nil/0 fall-through class:
`doc/08_tracking/bug/seed_value_match_no_arm_yields_nil_2026-11-02.md`,
`doc/08_tracking/bug/if_chain_match_no_arm_matched_is_silent_2026-10-10.md`.

## Rule

A `match` whose result is **used as a value** and that is **not exhaustive**
is a **compile-time error**, unless it has an unguarded catch-all arm.
Statement matches (result discarded) are not affected by this rule.

## Value position

A `match` is in value position when its result is consumed:

1. initializer of `val`/`var`, or right side of an assignment / compound assignment;
2. function or method argument, receiver, or operand of any operator;
3. element of an array/tuple/dict/struct literal or a string interpolation;
4. `return <match>` / `yield <match>` / a `?`/`??` operand;
5. the trailing (implicit-return) expression of a function or lambda whose
   return type is not `()`/unit (declared or inferred);
6. the trailing expression of a block, `if`/`elif`/`else` branch or `match`
   arm that is itself in value position (the rule propagates inward).

Anything else is statement position: an expression statement, the tail of a
unit-returning function, or a block/branch whose value is discarded.

## What counts as exhaustive

Checked in order; the first that applies decides.

| Scrutinee | Exhaustive when |
|---|---|
| any | an **unguarded catch-all** arm exists: `_`, `case _:`, or a bare lowercase binder (`other:`) — a binder is equivalent to `_` |
| `bool` | unguarded `true` **and** `false` arms |
| `Option<T>` / `T?` | unguarded `Some(<irrefutable>)` **and** `None`/`nil` arms |
| `Result<T,E>` | unguarded `Ok(<irrefutable>)` **and** `Err(<irrefutable>)` arms |
| enum (resolved owner) | every declared variant has an unguarded arm whose payload sub-patterns are all irrefutable (`_`, binders, field-binder shorthand). Payload variants count only through such arms; or-patterns (`A | B`) cover each alternative |
| `int`/`i*`/`u*`/`float`/`text`/`char`/tuple/struct/other | never by enumeration — a catch-all `_` is required |

Rules:
- A **guarded** arm (`case X if cond:`) covers nothing.
- A payload arm with a **refutable** sub-pattern (`Some(0)`, `Shape.Circle(1.0)`)
  covers nothing for that variant.
- **Enum resolution must be owner-qualified** (the MIR `enum_variant_index_q`
  owner key / HIR resolved symbol), never the bare-name registry: bare enum
  names collide (see `match_enum_fallthrough_silent_2026-08-01.md`). If the
  scrutinee's enum owner cannot be resolved unambiguously, the match is
  treated as **not provably exhaustive** (fail closed): the fix is `_` or a
  qualified arm. The message says "could not resolve enum owner".
- `unsafe:` blocks are checked the same way; this rule does not change unsafe
  semantics (no new nil is introduced; the catch-all must still be written).

## Fix guidance (for site sweeps)

Add an arm that is **not a silent nil/0**: either complete the variants, or
`_: panic("unreachable: <context>")` / `_: <meaningful default>` /
`_: Err(...)`. Never `_: nil`.

## Diagnostic

```
error[E-MATCH-NONEXHAUSTIVE-VALUE]: non-exhaustive match used as a value
  --> file.spl:LINE:COL
  scrutinee type: <type>; missing: <variants | "true"/"false" | "None" | "Err" | "non-literal values">
  help: add the missing arms or a `_:` arm (do not return nil)
```

In `warn` mode the same text is emitted as `warning[E-MATCH-NONEXHAUSTIVE-VALUE]`
and compilation continues (codegen keeps today's runtime panic/placeholder).

## Mode (staged rollout)

`value_match_exhaustiveness = warn | error` (default **warn** until the tree
reports 0 warnings and phase 3 has passed once; then the default flips to
`error` in a separate, coordinator-approved PR).

Precedence (highest first): CLI `--value-match-exhaustiveness=warn|error`,
env `SIMPLE_VALUE_MATCH_EXHAUSTIVENESS=warn|error`, SDN
`[compiler] value_match_exhaustiveness: "warn"` in the project/host config,
built-in default. Unknown values fall back to the default with a one-time
warning. `SIMPLE_SAFETY_PROFILE=critical` implies `error`.

## Placement

Pure-Simple compiler, after HIR lowering / type resolution (scrutinee type and
enum owner known), in `src/compiler/35.semantics/` (new
`value_match_exhaustiveness.spl`), reusing
`compiler.hir.match_coverage.ResolvedMatchCoverage` for the enum set
difference. The existing runtime fall-through panic remains as a backstop.
Seed (Rust) parity is optional; the seed must only keep compiling the
corrected source.

## Required tests (TDD)

One failing case per scrutinee class (enum, enum with payload, bool, Option,
Result, int, text, float), `_` silences each, bare binder silences, guarded
arm does not count, statement match unaffected, exhaustive enum passes,
ambiguous enum owner fails closed, `warn` mode reports but compiles.
