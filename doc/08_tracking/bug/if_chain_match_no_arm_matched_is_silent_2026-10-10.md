# If-chain match: "no arm matched" is silent

Status: OPEN. Severity: P2. Found 2026-10-10 while fixing dropped guards
(robustness item 3a). Not a guard defect; recorded so it is not mistaken for
one.

## What

A `match` whose arms are not all MIR-native (tuple, text literal, range,
struct, array patterns) is desugared by
`HirLowering.build_if_chain`
(`src/compiler/20.hir/hir_lowering/_Expressions/match_desugaring.spl`) into
nested `if`. Two tails are fail-open:

1. **A refutable last arm is unconditional.** `is_last` returns the arm block
   without testing its pattern, so

   ```simple
   match (a, b):
       case (1, y): 1
       case (2, y): 2      # last arm
   ```

   yields `2` for `(3, 0)`.

2. **A guarded last arm whose guard is false yields a placeholder.** Since the
   3a fix the guard is tested (`if guard: body` with no else), so the body no
   longer runs, but nothing traps: in value position the result is whatever
   the else-less `if` produces.

The guarded int path (`lower_guarded_scalar_match`) falls through the same way
(deliberately: it matches the seed for a statement match, where nothing runs).
In value position the seed raises "match expression exhausted without matching
any pattern"; the lowered code yields a placeholder instead. Only the enum path
traps, and only for guarded catch-alls with no unguarded default.

Status of evidence: (1) is by construction of `build_if_chain`, read from the
source, not executed. (2) lowers without diagnostics (statement position,
exercised while developing the fix); the value-position result was not
executed.

## Fix sketch

Give the chain a real tail: when the last arm is refutable or guarded, emit
the test and put a trap in the else branch. HIR has no trap node, so either
lower such matches as `MatchCase` and add tuple/text support to MIR, or build a
`panic(...)` call in the else block. Needs a count first: every non-exhaustive
if-chain match in the closure would start trapping where it now returns a
value, the same situation as the 286 enum matches in
`match_enum_fallthrough_silent_2026-08-01.md`.
