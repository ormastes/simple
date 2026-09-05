# Tuple-scrutinee match with enum sub-patterns collapses to the first arm

- **Filed:** 2026-08-21
- **Found by:** commit 419360fb240 (matchpat lane)
- **Status:** FIXED (pure-Simple HIR lowering; not yet deployed as a binary)
- **Severity:** miscompile — silently wrong runtime behaviour, no diagnostic
- **Component:** `src/compiler/20.hir/hir_lowering/_Expressions/match_desugaring.spl`

## Minimal repro

```simple
enum Color:
    Red
    Green
    Blue

fn pick(c: Color, n: i64) -> text:
    match (c, n):
        case (Color.Red, _):   "red-any"
        case (Color.Green, 0): "green-zero"
        case _:                "other"
```

Expected `pick(Color.Blue, 7) == "other"`. Under the pure-Simple HIR lowering
every input returned `"red-any"`, and the lowered HIR contained **zero**
`MatchCase` nodes — the whole match had become the first arm's body.

The AST is correct: it carries `PatternKind::Tuple` with `Enum` sub-patterns.
The defect is entirely in HIR lowering.

## Root cause

`build_match_expr` routes this match to the if-chain fallback: no arm has a
*top-level* `Enum` pattern (`has_enum == false`) and `Tuple` is not MIR-native,
so `needs_general_fallback` is true and `desugar_match_to_if_chain` runs.

`build_if_chain` asks `pattern_test_condition` for each arm's boolean test and
treats a `nil` answer as **unconditional** — it emits the arm's block directly
with no `If` wrapper and never recurses into the remaining arms.

`pattern_test_condition` ended in `case _: nil`. That catch-all silently
swallowed **five** `HirPatternKind` variants — `Enum`, `Array`, `Error`,
`CompleteRegion`, `DynRegion` — and reported all of them as *irrefutable*.
`Tuple` recurses into its elements and drops `nil` sub-conditions, so
`(Color.Red, _)` produced no conditions at all and the arm became
unconditional. Every later arm was then dead code.

The same `case _` was in `destructure_pattern_prelude`, where an `Enum`
sub-pattern's bindings (the `x` of `case (Some(x), 0):`) were silently left
**unbound**.

### Second, latent cause found while fixing this

`match_desugaring.spl` matched `HirPatternKind` values with arms written as
`case PatternKind.Wildcard:` — `PatternKind` is the *frontend AST* enum, a
different type. Those arms **never matched**; they only appeared to work
because the `case _` catch-all caught the fall-through. Four sites (two in
this file's two dispatchers, two inside `flatten_enum_match_arm`) plus
`pattern_is_mir_native` in `expression_components.spl`. In
`flatten_enum_match_arm` this meant a `_` payload slot was misclassified as
"complex" and driven into the `self.error(...)` path. Removing the catch-all
turned this from a hidden mis-dispatch into a hard `nil` return, which is how
it was found.

## Fix

`pattern_test_condition` is now EXHAUSTIVE over `HirPatternKind` with **no
`case _`**:

- `Wildcard`, `Binding` — explicitly irrefutable (HIR `Binding` carries no
  sub-pattern), `nil`.
- `Literal`, `Range`, `Or`, `Tuple`, `Struct` — unchanged.
- `Array(elements, rest)` — length test (`== n`, or `>= n` with a `rest`
  binding) AND-combined with the element sub-tests.
- `Enum(type, variant, payload)` — **always refutable**: a discriminant test
  AND-combined with the payload sub-tests. HIR has no discriminant-compare
  node, so the test is expressed as a nested single-level enum `MatchCase`
  yielding `true`/`false` with a trailing `_` arm — exactly the shape the
  pre-existing, tested MIR enum lowering already handles, so no new MIR
  support is needed. Payload slots are read back through the same idiom
  (`enum_payload_extract`), which is the only enum-payload accessor HIR/MIR
  agree on.
- `Error`, `CompleteRegion`, `DynRegion` — emit a loud
  **`E-HIR-MATCH-UNHANDLED-PATTERN`** diagnostic and return a *never-true*
  test, so later arms stay reachable. Never "unconditional".

`destructure_pattern_prelude` is likewise exhaustive, and now re-creates
bindings nested inside an enum payload (`enum_payload_prelude`) and inside an
array pattern. `rest` remains deliberately unbound (HIR has no slice
expression); `Or` bindings remain unsupported and documented.

`case PatternKind.X` → `case HirPatternKind.X` at all five mis-typed sites.

## Regression specs

- `test/01_unit/compiler/hir/tuple_match_enum_subpattern_spec.spl` (mirrored to
  `test/unit/`) — HIR level. Pre-fix **5 of 6 fail**, post-fix **6/6 pass**.
- `test/01_unit/compiler/hir/tuple_match_enum_subpattern_runtime_spec.spl`
  (mirrored) — behaviour: tuple of enum+int over three inputs, nested `Option`
  in a tuple, or-pattern inside a tuple. 5/5 pass. These pass on the Rust seed
  today (the seed's own interpreter lowers match correctly) and exist to fence
  the self-hosted lowering once deployed.
- `test/01_unit/compiler/hir/pattern_condition_mutability_source_spec.spl` —
  its `SOURCE` still pointed at `hir_lowering/expressions.spl`, a re-export
  shim since the `_Expressions` split, so it read a file with zero matches and
  was failing before this change. Repointed at `match_desugaring.spl` and the
  collector count updated 3 → 5.
