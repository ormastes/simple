# Lane FV4 — remaining §21.3 formal invariants (durability / atomicity / SC-donation)

Status: **DONE — sorry-free, gate GREEN**
Repo: /home/ormastes/dev/pub/simple
Date: 2026-07-27
Scope: extend the core-Lean-4 project `src/verification/os_enforcement/`
(lakefile pins `leanprover/lean4:v4.30.0`, EMPTY manifest = NO Mathlib, offline).
NOT committed — working copy only (per lane instructions).

## Gate result

```
cd src/verification/os_enforcement && lake build
✔ [10/11] Built OsEnforcement (496ms)
Build completed successfully (11 jobs).
```
- exit 0, `error` count = 0, `sorryAx` count = 0.
- `grep sorry|admit` over the 3 new files: only the word "sorry-free" in header comments.
- `#print axioms` on one theorem per module reports only `[propext, Quot.sound]`
  (and `does not depend on any axioms` for some) — **never `sorryAx`**.

## Files added (touched ONLY these + this state)

- `src/verification/os_enforcement/OsEnforcement/WalOrdering.lean` (new)
- `src/verification/os_enforcement/OsEnforcement/VfsTxnRecovery.lean` (new)
- `src/verification/os_enforcement/OsEnforcement/SchedDonation.lean` (new)
- `src/verification/os_enforcement/OsEnforcement.lean` (added 3 import lines)

## Module 1 — WalOrdering.lean  (§8.5/§15/§21 WAL-first rule)

Model: WAL is an ordered `List WalEvent` (`logWrite p | logFlush | dataWrite p |
commit`). `WalState = (logged, flushed, durable : List Nat)`. The enforcing
`step`: `logFlush` moves `logged → flushed`; `dataWrite p` is counted durable
ONLY if `p ∈ flushed`, else the state is unchanged (torn/lost-log drop).
`run` replays an event list. `durable_ok s := ∀ p ∈ s.durable, p ∈ s.flushed`.
Backs `src/os/port/sqlite/sqlite_vfs_contract.spl`.

Theorems (all CLOSED, sorry-free):
- WAL1 `wal_before_data` — for any event list from `WalState.empty`, `durable_ok
  (run ...)`: every durable data page has a flushed log record for the same page.
  (invariant preserved stepwise via `durable_ok_step` / `durable_ok_run`.)
- WAL2 `unflushed_data_not_durable` — a `dataWrite p` with `flushed.contains p =
  false` leaves `durable` unchanged (crash safety).
- WAL3 `commit_implies_flush` — `tryCommit s pages = some s'` ⇒ every page in
  `pages` is in `s.flushed` (commit ⇒ required flush ordering).
- helpers: `step_dataWrite_mem`, `step_dataWrite_not_mem`, `durable_ok_step`,
  `durable_ok_run`.

## Module 2 — VfsTxnRecovery.lean  (§21 "recover to pre-state or committed")

Model: `Txn = (preState, committed : Bool, pending : Nat)`;
`committedState t := t.pending`; `recover t := if committed then pending else
preState`.

Theorems (all CLOSED, sorry-free):
- TXN1 `recover_is_prestate_or_committed` — `recover t = preState ∨ recover t =
  committedState t` (never a torn intermediate).
- TXN2 `uncommitted_rolls_back` — `committed=false ⇒ recover = preState`.
- TXN3 `committed_persists` — `committed=true ⇒ recover = committedState`.

## Module 3 — SchedDonation.lean  (§21 "SC-donation returned or cancelled")

Model: `Donation = (clientBudget, serverBorrowed, returned : Bool)`.
`donate` moves client→server; `complete`/`cancel` move server→client and mark
settled; `total d := clientBudget + serverBorrowed`.

Theorems (all CLOSED, sorry-free):
- SD1 `donation_returned_on_complete` — `serverBorrowed=0 ⇒ (complete (donate
  d)).clientBudget = d.clientBudget` (fully returned).
- SD2 `donation_returned_on_cancel` — same for `cancel`.
- SD3 `no_budget_leak` — `total` invariant across donate / complete / cancel
  (conservation: nothing created or destroyed). Uses core `omega`.

## Blocked rows

NONE. All 9 theorems (WAL1-3, TXN1-3, SD1-3) closed sorry-free.

## LANDMINE recorded (for future FV lanes)

Parallel harden sessions force-push `main` continuously; during this lane a jj
sync **twice** clobbered the working copy: (1) deleted the 3 new module files and
reverted the root import edits, and (2) injected `<<<<<<< Conflict / +++++++ side
#1 / %%%%%%% side #2` jj-conflict markers directly INTO `WalOrdering.lean` and the
root `OsEnforcement.lean`, breaking the build with "invalid import command".
Resolution that worked: re-`Write` the clean file content (my new modules are the
sole author, so my content is authoritative) and re-generate the root import list
from `ls OsEnforcement/*.lean`, then build immediately before the next sync tick.
Do NOT hand-merge markers — overwrite. `grep -rlE '^(<<<<<<<|%%%%%%%|\+\+\+\+\+\+\+)'`
over the module dir is the fast detector.

Two Lean-idiom gotchas also hit (fixed):
- `simp` has a global `List.contains → ∈` rewrite, so a hypothesis `xs.contains x
  = true/false` becomes inapplicable inside `simp`. Reduce the `step` `if` via
  `simp only [step]` + `split` + `List.contains_iff_mem.{mp,mpr}` instead.
- `unfold step` does NOT reduce the `match` to the inner `if`; use `simp only
  [step]` to expose the `if` before `split`/`if_pos`/`if_neg`.

## Resume / re-verify command

```bash
cd /home/ormastes/dev/pub/simple/src/verification/os_enforcement
export PATH="$HOME/.elan/bin:$PATH"
lake build
grep -nE '\b(sorry|admit)\b' OsEnforcement/{WalOrdering,VfsTxnRecovery,SchedDonation}.lean
```
Expect: `Build completed successfully (11 jobs).`, exit 0, no real sorry/admit.
If markers reappear after a sync: re-Write the clean modules + regenerate root
imports, then rebuild.
