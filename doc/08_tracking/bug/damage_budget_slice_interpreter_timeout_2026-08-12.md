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

## 2026-11-10 P3 triage (work/p3-interp-20261110) — SUPERSEDED (timeout no longer reproduces)

Fresh scoped isolation, direct seed invocation (no test daemon), deployed
Windows Rust seed, worktree bin/simple.exe, 150 s hard cap:

    test test/01_unit/lib/common/ui/render_opt/damage_budget_slice_spec.spl

Verdict: 4/4 PASS in ~3.2 s (exact partition expectations all green, which is
the exact-partition parity the record asked for). The 120 s worker-budget
timeout does not reproduce on the current seed + source; runtime
nontermination is disproven for this spec, consistent with the root cause
having been compiler-closure complexity (the same cross-module
class/dispatch family fixed by the 2026-11-07 seed) rather than the slicer
itself.

Not done here, per this record's own prohibition: the slicer was NOT wired
into WM/Web/GUI production; that admission decision (and a daemon-mode
re-check, plus replay-checksum parity against recorded frames) stays with the
owning UI/render lane.
