# Match guard-count invariant (E-MIR-MATCH-GUARD)

## What it prevents

`case P if g:` must run its body only when `P` matches **and** `g` is true. If
a lowering step forgets the guard, the arm runs whenever `P` matches. Nothing
crashes and nothing is reported; the program just takes the wrong arm.

The invariant: **every guard the parser produced is evaluated by the lowered
code.** It is checked at the two places a guard can be lost.

| Half | Where | Compares | Diagnostic |
|---|---|---|---|
| HIR | `HirLowering.build_match_expr` (`20.hir/hir_lowering/_Expressions/match_desugaring.spl`) | guarded arms parsed vs guards carried by the result (guarded `MatchCase` arms + if-chain guard tests) | `E-HIR-MATCH-GUARD` |
| MIR | `MirLowering.lower_match_case` (`50.mir/_MirLoweringExpr/expr_dispatch.spl`) | guarded arms HIR handed over vs guard branches emitted | `E-MIR-MATCH-GUARD` |

The MIR half is exact (`==`). Its two counters live on the lowering
(`match_guards_expected`, `match_guards_lowered`) and are saved and restored
around each match, so a match nested in an arm body is checked on its own.
Only two things may change the expectation, and both say so at the site:

- the or-arm split in `lower_enum_match` (`case A(x) | B(x) if g:` becomes one
  guarded arm per alternative, so the expectation grows by `alternatives - 1`);
- an arm skipped because it follows an unguarded catch-all (unreachable, its
  guard is legitimately never evaluated).

The HIR half is `carried >= parsed` for the `MatchCase` path (or-arms multiply)
and exact for the if-chain path.

## How it reports

```
E-MIR-MATCH-GUARD: match in fn <module>.<fn> (module <module>) has 1 guard(s) to
evaluate but lowered 0 guard branch(es); a guard was dropped and its arm would
run unconditionally
```

with the match's span. The HIR message names the function and the two counts
the same way.

Channel, at the default level `warning`:

- MIR half: `MirLowering.advisory("E-MIR-MATCH-GUARD", ...)`, i.e. the
  `mir_advisories` list, **never** `MirLowering.errors` (several routes treat
  `errors.len() > 0` as fatal). The driver prints advisories as warnings.
- HIR half: `HirLowering.recovered(...)`, the HIR warning channel
  (`LoweringErrorKind.Recovered`), which the driver reports as warnings.

A second, never-fatal message covers guards that are counted as accounted for
because their arm cannot run:

```
W-HIR-MATCH-GUARD-UNREACHABLE: 7 guarded match arm(s) follow arm 3, whose
pattern is irrefutable (it only binds) and has no guard; they can never run and
their guards are never evaluated [level: E-MIR-MATCH-GUARD]
```

This is usually a pattern that binds where a variant test was meant, e.g. a
bare unit variant inside a tuple pattern
(`doc/08_tracking/bug/bare_unit_variant_in_tuple_pattern_binds_2026-10-10.md`).
The enum-match path reports the same situation with MIR's existing
`unreachable match arm` warning.

## Level switch

One id for both halves, the lowering advisory id `E-MIR-MATCH-GUARD`
(`src/compiler/50.mir/mir_verify_levels.spl`), same switch as the MIR verifier
rules:

```
SIMPLE_MIR_VERIFY_LEVELS="E-MIR-MATCH-GUARD=error"     # fatal: error_fatal / HIR error
SIMPLE_MIR_VERIFY_LEVELS="E-MIR-MATCH-GUARD=warning"   # default (warn-first)
SIMPLE_MIR_VERIFY_LEVELS="E-MIR-MATCH-GUARD=off"       # skips the counting, not just the report
```

`*=<level>` applies to every id not named. A malformed spec is rejected as a
whole and leaves the default. The level is resolved once per lowering instance.

## Promotion criterion (warning -> error)

Make `E-MIR-MATCH-GUARD` default to `error` when **both** hold on the same commit:

1. the census (below) reports `hits=0` over every file in `src/` that contains
   a guard, and
2. a phase-3 + phase-4 full-closure build prints no `E-HIR-MATCH-GUARD` and no
   `E-MIR-MATCH-GUARD`.

(1) is recorded in `C:/dev/simple-bootstrap-storage/robustness/items/match-guard-invariant_STATUS.md`.
(2) needs a bootstrap run and is the only open step.

## Census on real modules

```
MATCH_GUARD_CENSUS_FILES=src/a.spl,src/b.spl \
  <simple> test test/01_unit/compiler/50.mir/match_guard/match_guard_census_spec.spl
```

Lowers each file on its own (parse -> HIR -> MIR, no import closure) and prints
`GUARD-CENSUS <path> guarded_arms=<n> hits=<n>` plus one `GUARD-HIT` per hit.
`GUARD-UNREACHABLE` lines list the warning above; they do not count as hits.
Without the variable it runs on `src/compiler/30.types/type_infer/core.spl`,
whose `unify` has nine guarded tuple arms.

Measured 2026-10-10 (38 of the 41 guard-containing files under `src/`, 108
textual guarded arms; 3 files cannot be lowered by the harness): **0 hits**.
With the if-chain fix reverted the same census reports 2 matches / 3 dropped
guards (`type_infer/core.spl` `unify`, `app/interpreter/utils/collection_ops.spl`
`bind_sequence_pattern`); see
`doc/08_tracking/bug/match_guard_dropped_by_if_chain_desugar_2026-10-10.md`.

## Adding a case

- A new arm shape: add a function between the `SHAPES` markers in
  `test/01_unit/compiler/50.mir/match_guard/match_guard_parity_spec.spl` plus an
  `r_<name>()` driver that packs its results into one integer, then an `it`.
  The function is real code, so the seed interpreter is the oracle; the same
  text is lowered and the MIR is inspected (and executed where possible).
- A new lowering path that emits a guard branch: increment
  `self.match_guards_lowered` next to the `terminate_if(guard, ...)`. A path
  that forgets is reported by the invariant the first time a guarded arm
  reaches it.
- A new path that legitimately does not lower a guard: adjust
  `self.match_guards_expected` at that site with a comment saying why.

## Known limits

- **Counts, not identities.** The check proves the right number of guard
  branches exists, not that each branch tests the right expression.
- **HIR `MatchCase` path is `>=`.** A transformation that drops one
  alternative's guard of an or-arm while keeping another's is not caught there;
  the MIR half catches it only if the alternative still arrives guarded.
- **Enum and text shapes are verified structurally**, not executed: the MIR
  interpreter has no enum-discriminant or text-equality runtime. Int and
  tuple-of-int shapes are executed and compared with the oracle.
- **No stage-2 native execution** is part of the spec; the "stage-2 path" here
  is the pure-Simple HIR/MIR lowering run inside the seed interpreter.
- A guarded int match is lowered as an if-chain, never as a jump table.
- If-chain matches (tuple, text, range, struct, array patterns) still treat a
  refutable **last** arm as unconditional, and a guarded last arm whose guard is
  false yields the placeholder value instead of trapping:
  `doc/08_tracking/bug/if_chain_match_no_arm_matched_is_silent_2026-10-10.md`.
- The seed interpreter itself ignores a guard on a wildcard arm
  (`case _ if c:`), so it is not a valid oracle for that one shape:
  `doc/08_tracking/bug/seed_interp_wildcard_arm_guard_ignored_2026-10-10.md`.
