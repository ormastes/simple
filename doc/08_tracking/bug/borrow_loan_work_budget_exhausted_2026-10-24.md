# Borrow check "loan liveness work budget exhausted" on the 204-module Phase-3 closure (2026-10-24)

Symptom: six module functions fail with `loan liveness work budget exhausted`
(point ids 79, 521, 813, 1013, 2325, 3689; diagnostics are unattributed, no
module name). Under `--go-to-end` the driver absorbed the errors and called
`go_to_end_finish_v1(0, [])`, so zero objects were emitted for all modules.

Root cause 1 (budget): `NLLChecker.solve_loans`
(src/compiler/55.borrow/borrow_check/nll.spl) hard-coded `work > 1000000`.
The liveness fixed point and the CFG walk use O(n^2) array `contains` /
`push` set operations over locals and `LoanAlias` lists.

Workaround, now removed (it was tagged `workaround(borrow-work-budget)`):
`SIMPLE_BORROW_WORK_BUDGET` overrode the budget, and unset or malformed kept
1000000. observation_v4 needed 2e8 under it.

Real fix (replaces the workaround; `SIMPLE_BORROW_WORK_BUDGET` is gone):

- Liveness sets are sorted, duplicate-free `[i64]` arrays (`nll_sorted_*`):
  binary-search membership, linear-merge union/difference/equality. A point
  transfer is O(|uses| + |defs| + |live|), not O(|live|^2).
- Each reachable block is summarized once as `live_in = gen U (live_out - kill)`.
  A worklist seeded in postorder requeues a block's predecessors (built from
  `successors`, not `block.predecessors`) only when its `live_in` changed. One
  final backward walk per block writes the per-point `before`/`after` sets.
  Cost: O(B*L) per sweep plus O(P*L) once (B blocks, P points, L live locals),
  and visits are at most B + E*L. The old round-robin walked blocks in
  reverse postorder, which is the wrong order for a backward analysis, so a
  fact crossed only one block per round: about B rounds of O(P*L^2).
- Budget stays fail-closed at 1,000,000, in real units. Liveness charges
  `1 + |live_in|` per block transfer. The loan CFG walk keeps
  `1 + |aliases|` per point transfer, on its own counter.
- `nll_live_aliases` uses binary search on the sorted live set.
- Residual: `loan_alias_union` / `loan_alias_contains` (LoanAlias lists) are
  still quadratic. They were left alone on purpose, because their order
  determines diagnostic order.

Evidence (Rust seed interpreter, same binary mtime 2026-10-23 12:18:03):

- `test/01_unit/compiler/borrow/nll_large_function_spec.spl` (700-block chain
  and loop): before, 3/4 failed with the budget error in 53 s; after, 4/4 pass in 2 s.
- `build/repro/nll_scale_probe.spl` (2000 blocks, nested loops, 100 locals):
  before, `loan liveness work budget exhausted`; after, `ok=true`.
- Differential probe of 600 random CFGs (loops, branches, unreachable
  blocks, copies, projections; 556 diagnostics): verdicts and diagnostic
  text are byte-identical before and after.
- Every `test/01_unit/compiler/borrow/*_spec.spl`, the semantics borrow spec and
  `test/fixtures/compiler/nogc_nll_flow_probe.spl`: identical output before and
  after (24 files, modulo seed `TypeId(n)` numbering in warnings), pre-existing
  seed-lane failures included.
- Not re-run: the Phase-3 closure (it needs a Stage 2 rebuild).

Root cause 2 (blast radius): `CompilerDriver.borrow_check()` appended every
failure to `ctx.errors`; both the unstaged path and the staged flush gate
("no object once any error is recorded") then dropped all objects. Fixed:
under go-to-end, a failing module is recorded in the ledger (stage `borrow`),
excluded and evicted from `ctx.mir_modules`; others still emit objects and the
build still ends as a go-to-end failure with no link.
