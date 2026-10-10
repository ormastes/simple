# A bare unit variant inside a tuple pattern binds instead of testing the variant

Status: OPEN. Severity: P1 (silent wrong code in the compiler's own type
unifier on the stage-2 path). Found 2026-10-10 by the new
`W-HIR-MATCH-GUARD-UNREACHABLE` warning (robustness item 3a). Belongs to the
bare-variant family (item 2a); not fixed here.

## What

```simple
enum S:
    P(i64)
    Q(i64)
    R

fn f(a: S, b: S) -> i64:
    match (a, b):
        case (S.P(x), S.P(y)) if x == y: 1
        case (R, R): 2                    # binds two variables named R
        case (S.Q(x), _) if x > 5: 3      # unreachable
        case _: 9
```

`lower_match_pattern` resolves a bare name against the subject's enum only
when the subject type is a known `HirTypeKind.Tuple` of named enums. A tuple
*literal* scrutinee `(a, b)` carries no type at HIR lowering, so each element
falls to `lower_pattern` and `R` becomes `HirPatternKind.Binding`. The if-chain
then treats `(R, R)` as irrefutable: it is taken for every value arms above it
rejected, and every arm below it is dead. The enum being declared in the same
file does not help. Top-level bare arms do not have this problem (MIR
reclassifies them); the tuple path never reaches that code.

## Live site

`src/compiler/30.types/type_infer/core.spl` `unify`:

```simple
match (ty1.kind, ty2.kind):
    case (Int(b1, s1), Int(b2, s2)) if b1 == b2 and s1 == s2: Ok(())
    case (Float(b1), Float(b2)) if b1 == b2: Ok(())
    case (Bool, Bool): Ok(())      # arm 3: catch-all on the stage-2 path
    case (Char, Char): ...
    ...                            # 7 guarded arms and everything else: dead
```

On the stage-2 path `unify` returns `Ok(())` for every pair the first two arms
reject. The census reports it as
`W-HIR-MATCH-GUARD-UNREACHABLE: 7 guarded match arm(s) follow arm 3`.

Evidence level: structural (the lowered HIR/MIR and the warning, single-file
harness and an in-file enum fixture pinned in
`test/01_unit/compiler/50.mir/match_guard/match_guard_invariant_acceptance_spec.spl`).
Not executed natively. Whether the bootstrap pipeline calls this `unify` was
not established.

## Detection today

Only matches where a guarded arm follows the binding arm are reported. A match
with no guards after the accidental catch-all is not detected by this warning.

## Fix options

1. Source: qualify the unit variants at the site (`HirTypeKind.Bool`, ...).
   Changes stage-2 type-unification behaviour from "everything unifies" to the
   intended rule, so it needs a bootstrap run.
2. Lowering: give tuple-literal scrutinees per-slot subject types, and apply the
   unique-unit-variant-owner fallback MIR already uses for top-level bare arms.
   Same ambiguity policy as item 2a.
