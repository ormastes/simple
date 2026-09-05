# Progressive damage slicer interpreter timeout — 2026-08-12

Status: OPEN; implementation present but not admitted to production.

`common.ui.render_opt.damage_budget_slice` was added to partition an exact
over-budget `DamageFramePlan` into current and deferred rectangles without
widening or omission. Its focused four-example spec repeatedly reaches the
test daemon's 120-second worker budget before a useful verdict.

Three bounded verify/fix cycles were exhausted:

1. initial flat-array implementation timed out;
2. array-mutating helper was inlined to avoid value-semantics copies, timed out;
3. compact semicolon statements were expanded to ordinary statements, timed
   out.

No PASS is claimed. Do not wire the slicer into WM/Web/GUI production until a
fresh scoped session isolates whether the issue is compiler complexity,
test-daemon cache/state, or runtime nontermination and obtains exact partition
and replay checksum parity. The already-passing binary budget scheduler remains
usable for admit/defer receipts.
