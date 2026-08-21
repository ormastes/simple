# Union narrowing has no grammar and no runtime lowering (lane S4 follow-up)

- **Date:** 2026-08-21
- **Lane:** Wave 2D / Phase 4, S4 (union normalization)
- **Status:** RESOLVED (2026-08-21) for grammar, lowering and exhaustiveness; the RUNTIME-EXECUTION claim is explicitly NOT made — see "What is still not proven" below.

## What works after S4

`i64 | f64 | bool | text` now survives the flat-AST bridge as a real
`TypeKind.Union` -> `HirTypeKind.Union` -> `MirTypeKind.Union` (tagged), and
`compiler.semantics.union_normalize` synthesizes the canonical `@closed` enum
`__Union_bool_f64_i64_text` for it, which reaches the enum-contract table as
`contract=closed`. Gated by `scripts/check/check-closed-match-coverage.shs`
(fixture `test/fixtures/enum_contract/union_closed.spl`).

## What does not

There is no surface syntax for narrowing a union value, and no lowering behind
either candidate spelling. Measured on the seed at `bin/simple`:

1. `match x:` / `case i64 v:` — **parse error**:
   `Unexpected token: expected -> or => or :, found Identifier { name: "v" }`.
   A type-plus-binding arm is not in the grammar.
2. `if x is i64:` — **parses, then miscompiles**: the type name is lowered as a
   VALUE, giving
   `GlobalLoad: unresolved identifier 'i64' (not a global, function,
   const-data name, or import)` and a codegen stub fallback. `is` against a
   type is not wired for unions. `35.semantics/narrowing.spl:416` still carries
   the stale comment "Full union narrowing requires HirTypeKind.Union variant
   (not yet in HIR)" — the variant HAS existed; the narrowing was never built.

So a union-typed value can be declared and carried, but not discriminated, and
an exhaustiveness miss over a union cannot yet be reported as E-CLOSED-001 at a
real match site (the synthesized enum is contracted, but no source match names
its variants).

## Required to close

- Grammar for a narrowing arm (`case i64 v:` or equivalent) in the parser's
  match-arm rule.
- Lowering of that arm to `HirPatternKind.Enum(__Union_..., <VariantName>,
  payload)` against the synthesized enum, so the EXISTING closed-enum coverage
  check reports the miss with no new rule.
- `x is T` on a union lowering to a discriminant test rather than a global load.

Until then, do not claim S4 runtime narrowing; the normalization half is done
and gated, the narrowing half is not.

## Resolution (2026-08-21)

### Grammar chosen

A type-pattern arm in the position an enum-variant arm already occupies. §10.3
requires "exhaustive narrowing" but fixes no spelling, so this is the smallest
form consistent with existing match arms:

```simple
fn narrow(x: i64 | f64 | bool | text) -> i64:
    match x:
        case i64 v: v
        case f64 f: 2
        case bool b: 3
        case text s: 4
```

`case nil:` keeps its existing spelling and now denotes the union's `nil`
member (`T?` expands to `T | nil` as a member). `x is i64` is a real type test.

Recognition mirrors the `case complete b:` / `case dyn b:` region arms: two
juxtaposed identifiers are not an expression in any Simple grammar, so the arm
is recognised in the match-arm parser and lowered to the marker call
`__type_test(T, b)`. Nothing existing can be stolen by it, and the head token
must LOOK like a type (builtin scalar, or uppercase-initial) so an ordinary
`foo bar` still reaches the expression parser and its existing error.

### How it works

`case i64 v:` is rewritten in HIR lowering into the equivalent variant arm of
the synthesized `@closed` enum S4 already builds:
`Enum(__Union_bool_f64_i64_text, I64, Tuple([Binding(v)]))`. After that rewrite
the match is an ORDINARY enum match, so coverage, the closed contract and
E-CLOSED-001 govern it with no union-specific checker and no second
exhaustiveness rule. The rewrite happens in `build_match_expr` because that is
the last point at which a match is still a match: an arm kind MIR does not
natively handle makes the whole match desugar into an if-chain, which erases
the MatchCase node exhaustiveness reads.

The scrutinee's union type comes from the SYMBOL TABLE (a parameter's or
annotated local's declared type), not from `HirExpr.type_`, which is still nil
at that point. That bounds what is narrowable to values with a WRITTEN union
type, and the bound is loud, never silent: a type pattern whose scrutinee is
not a known union is **E-NARROW-001**, and a type pattern naming a non-member
of the union is **E-NARROW-002**.

Also fixed on the way: `case nil:` was NOT in the flat-AST bridge's literal
list and fell through to the Wildcard catch-all, so it silently matched every
scrutinee — the same defect class the EXPR_BINARY and EXPR_TUPLE cases were
added to fix.

### Files

- `src/compiler/10.frontend/core/_ParserStmt/match_type_pattern.spl` (new) — grammar
- `src/compiler/10.frontend/core/parser_stmts.spl` — one hook in the arm loop
- `src/compiler/10.frontend/parser_types_expr.spl` — `PatternKind.TypeTest` (appended LAST)
- `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` — marker -> TypeTest; nil-literal fix
- `src/compiler/20.hir/hir_definitions.spl` — `HirPatternKind.TypeTest`, `HirExprKind.TypeTest` (both LAST)
- `src/compiler/20.hir/hir_lowering/_Expressions/union_narrow_arms.spl` (new) — the rewrite + E-NARROW-001/002
- `src/compiler/20.hir/hir_lowering/_Expressions/type_test_operand.spl` (new) — `x is T` type-operand rule
- `src/compiler/20.hir/hir_lowering/_Expressions/{expression_core,expression_components,match_desugaring}.spl`
- `src/compiler/35.semantics/union_normalize/narrow.spl` (new) — name mapping, E-NARROW-001 text
- `src/compiler/35.semantics/enum_contract/hir_match_coverage.spl` — TypeTest is not a wildcard
- `src/compiler/40.mono/monomorphize/hir_subst/body_subst.spl` — exhaustive walker
- `src/compiler/10.frontend/core/interpreter/eval.spl` — tree-walk `__type_test` matching
- regenerated: `spec/compiler_schema/registry/**`, `src/compiler/20.hir/generated/**`, `src/compiler/10.frontend/generated/ast_visitor.spl`

### Evidence

- `test/01_unit/compiler/semantics/union_narrowing_spec.spl` — 10/10 (grammar,
  rewrite-to-variant-arms, non-exhaustive miss, `case nil:` as a member,
  E-NARROW-001 on a non-union scrutinee, `x is T` vs `x is y`).
- `sh scripts/check/check-closed-match-coverage.shs` — `PASS — 2 match(es)
  checked, non-exhaustive=0 wildcard-closed-critical=0 (1 union sum(s), 2
  contracted across 2 module(s))`. The union fixture now carries a real
  narrowing match, and a new NEGATIVE fixture
  (`test/fixtures/enum_contract/union_nonexhaustive.spl`, 3 of 4 members, no
  wildcard) is a fatal selftest case that must come out non-exhaustive.
- Unchanged green: union_normalize 14/14, enum_contract_hir_wiring 10/10,
  tuple_match_enum_subpattern 6/6, match_arm_underscore_subpattern 5/5,
  hir_subst_body 8/8, generated_visitor_coverage 11/11.

### What is still not proven

**Runtime EXECUTION of a narrowing match is implemented but not demonstrated
here.** The tree-walk interpreter (`10.frontend/core/interpreter/eval.spl`)
matches `__type_test` against the runtime value kind and binds the narrowed
value, but no evidence run exists, because `bin/simple` is currently the RUST
SEED: its own parser has no type-pattern grammar, so `bin/simple run` over a
narrowing source proves nothing about this change, and driving the pure-Simple
interpreter in-process under the seed fails on unrelated seed module-state
limits (`variable 'cache_initialized' not found`). Demonstrating it needs a
deployed self-hosted binary — the same blocker as the stage-binaries guard in
`.claude/rules/vcs.md`. Do not claim runtime narrowing until that run exists.
