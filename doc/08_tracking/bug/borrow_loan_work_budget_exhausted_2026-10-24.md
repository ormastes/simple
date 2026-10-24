# Borrow check "loan liveness work budget exhausted" on the 204-module Phase-3 closure (2026-10-24)

Symptom: six module functions fail with `loan liveness work budget exhausted`
(point ids 79, 521, 813, 1013, 2325, 3689; diagnostics are unattributed, no
module name). Under `--go-to-end` the driver absorbed the errors and called
`go_to_end_finish_v1(0, [])`, so zero objects were emitted for all modules.

Root cause 1 (budget): `NLLChecker.solve_loans`
(src/compiler/55.borrow/borrow_check/nll.spl) hard-coded `work > 1000000`.
The liveness fixed point and the CFG walk use O(n^2) array `contains` /
`push` set operations over locals and `LoanAlias` lists.

Workaround (tagged `workaround(borrow-work-budget)`): `SIMPLE_BORROW_WORK_BUDGET`
overrides the budget; unset or malformed keeps 1000000.

Real fix (open): replace the array set ops in `solve_loans`, `loan_alias_union`
and `nll_live_aliases` with Dict-based membership sets so work is O(n).

Root cause 2 (blast radius): `CompilerDriver.borrow_check()` appended every
failure to `ctx.errors`; both the unstaged path and the staged flush gate
("no object once any error is recorded") then dropped all objects. Fixed:
under go-to-end, a failing module is recorded in the ledger (stage `borrow`),
excluded and evicted from `ctx.mir_modules`; others still emit objects and the
build still ends as a go-to-end failure with no link.
