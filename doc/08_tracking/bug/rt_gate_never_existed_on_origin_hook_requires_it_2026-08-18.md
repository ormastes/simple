# The rt_ gate has never existed on origin/main, yet the push hook requires it

Status: OPEN. Filed 2026-08-18 (found during a push attempt).
Related: `jj_push_bypasses_rules_sdl_gates_2026-08-11.md`,
`fourth_tree_wipe_6f86ff32a7d_guard_not_enforced_2026-08-11.md` (same class:
a guard believed to be enforcing while it was not).

## Finding

`scripts/check/check-no-direct-rt.shs` does not exist anywhere in
`origin/main`'s committed history. It has only ever existed as an uncommitted
file in local working trees. Verified from a clean worktree checked out at
`origin/main` during a cherry-pick push attempt: the file is absent, and the
guard therefore cannot run for anyone who clones the repo.

Meanwhile `scripts/check/pre-push-conflict-tree-guard.shs` (as of
2026-08-18, line ~218/247/837) hard-requires the file: it is added to the
existence-check loop and invoked via `run_guard`.

## Consequences

1. **The rt_ ratchet has never been enforced on a real push to origin.** Every
   push to date either bypassed the hook or ran from a working tree that
   happened to carry the uncommitted file.
2. The measured baseline (`scripts/check/no_direct_rt_baseline.txt`, 12,668 on
   2026-08-18) describes local state only; nothing prevents an origin-side
   regression above it.
3. A clean clone that DOES run the hook now hits the existence check for a
   missing file — behaviour depends on whether that check is fail-closed.

## Wanted

Commit and push `check-no-direct-rt.shs`, its allowlist
(`no_direct_rt_allowlist.txt`) and baseline (`no_direct_rt_baseline.txt`)
together, then verify from a **clean clone** that the hook finds and runs it —
per the Fix test standard, the reproduce evidence is a clean-clone run, not a
run in a working tree that already has the file.

A preserved branch containing the restoration commit exists locally:
`session-2026-08-18-pickup` (tip `518dfa6adf8`); the push itself is blocked on
`committed_tree_unbuildable_only_dirty_worktree_compiles_2026-08-18.md`.


---

## Lane disposition 2026-11-13 (p3-misc-b)

hook-vs-history mismatch; the push-hook owner must either land the gate or drop the requirement. Record only.

## Reconciliation 2026-11-27 (Windows host, W4-7) — hook/script contract reconciled; row stays `open` for baseline/paydown decision

1. **Hook/manifest/script contract reconciled:**
   - Verified `scripts/check/check-no-direct-rt.shs`, `scripts/check/no_direct_rt_allowlist.txt`, and `scripts/check/no_direct_rt_baseline.txt` (`6290`) are tracked on `HEAD` and wired into `config/check/must_check_gates.sdn` (`push-no-direct-rt`, `push_blocking=false`, `mode=ref`, `advisory since 2026-09-23`, run when `MUST_CHECK_ADVISORY=1`) and `scripts/check/check-push-must-pass.shs` (`--roots src --rev $_ref --baseline-rev $_direct_rt_base`).
   - Updated stale comments in `scripts/check/check-no-direct-rt.shs` (line 28 previously claimed `push-no-direct-rt (push, blocking)` and `baseline 7776`) and `scripts/check/check-push-must-pass.shs` (previously claimed `MANDATORY pre-push gate`) so both accurately match `must_check_gates.sdn` (`push_blocking=false`, advisory unless `MUST_CHECK_ADVISORY=1`).
   - Replaced the slow per-file bash `while read` allowlist loop in `scripts/check/check-no-direct-rt.shs` (`scan_dir`) with a single `LC_ALL=C awk` pass (`suffix:`, trailing `/`, exact path, comments, CRLF, `decls` subtraction, offender output), and added selftest fixture 24 covering allowlist and offender formatting.
2. **Verified:**
   - `check-no-direct-rt.shs --selftest-only`: `PASS — 24 selftest fixture(s) checked (rg-vs-grep parity exercised)`
   - `check-push-must-pass.shs --self-test`: `PASS — 34 ledger/budget/dispatcher/rebase/stale-merge fixtures checked`
   - `check-hook-installation.shs --selftest` (`7` passed), `--selftest-paths` (`9` cases PASS), live `check-hook-installation.shs` (`PASS — 12 check(s) performed, hook wiring intact`)
   - Measured `NO_DIRECT_RT_SELFTEST_CHILD=1 sh scripts/check/check-no-direct-rt.shs --roots src --rev HEAD` -> `scanned_files: 20071, direct_total: 13512, allowed_provider: 6545, forbidden_product: 6967, extern_declarations: 6736`, exit `1` because `6967 > 6290` baseline (`99.55s` in isolated single-check run).
3. **Why row remains `open`:** Standalone `--roots src` remains `6967` vs `6290` baseline (`677` over). Paying down those direct `rt_*` call sites or deliberately updating `no_direct_rt_baseline.txt` via `--generate-baseline` requires an owner policy decision (never silently re-baselined by a verification lane).
