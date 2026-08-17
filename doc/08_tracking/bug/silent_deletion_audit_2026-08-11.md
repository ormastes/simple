# CLOSED 2026-08-17 — all 12 rows re-verified; 0 genuine deletions outstanding

**Nothing is missing. No restoration was required.** Every row was re-checked
against both the working tree and a freshly-fetched `origin/main`
(`ff4534c0dc1`). Full evidence in "Re-verification" below.

**But this audit was wrong twice, in opposite directions, and the reason is one
mechanical defect worth more than the audit itself — see "What the methodology
got wrong". In short: it analysed 1.2% of its own dataset and reported
completeness.**

## Re-verification 2026-08-17 (every row)

| row | claim | verdict now | evidence |
|---|---|---|---|
| 1,2 | 427-file sweep `7731b4c1394`, reverted by `ad2b5d5307f` | **TRUE, resolved** | `scripts/check/directory_fanout_baseline.txt` present at exactly 1009 lines (the audit's own max-deletion figure) |
| 3 | collections.rs "STILL MISSING", 70 fns absent | **FALSE ALARM** | 6199 lines / 210 `fn rt_*` in worktree, 6122 on origin. All 8 symbols the audit named as absent are present: `rt_array_free_deep`, `rt_array_reduce`, `rt_push`, `rt_pop`, `rt_drop`, `rt_find`, `deep_free_classify`, `collection_provider_cache` |
| 4,5,9,10,11,12 | INTENTIONAL spec rewrites | **TRUE** | all named specs present on origin/main |
| 6 | `cipher_sha256_provider.spl` deleted 226→0, restored later | **TRUE, resolved** | present at exactly 226 lines, `src/lib/nogc_sync_mut/spec/evidence/counterpart/` |
| 7 | `simd_phase9c.spl` deleted with archive copies | **TRUE** | archive present at `doc/05_design/compiler/phases/simd_phase9c.spl` |
| 8 | dead CSS lane removed, superseded by `dom_color.spl` | **TRUE** | `src/lib/gc_async_mut/gpu/browser_engine/dom_color.spl` present |

Current tree health: 114,815 files; `src/` 16 entries (guard band 13..25);
`src/runtime` 218 files (canary floor 150). All green.

## What the methodology got wrong

### Defect 1 — it analysed 1.2% of its own dataset and called it complete
The audit states it pulled diffstat "in one pass (`git log --numstat`, **2714
file-change rows**)". Re-running that same scan over the same window yields
**229,025 rows**. The audit saw **1.2%** of its data and concluded
*"No new, still-unaddressed silent deletions were found."*

The `2714` figure is the fingerprint of the failure: output was truncated
(capped tool output, or a `head`/pipe limit) and the truncated slice was treated
as the whole. This is the same error family as reading exit 0 with no verdict
line as green — **absence of data mistaken for absence of findings**. An audit
must assert its own input size before drawing a negative conclusion.

### Defect 2 — the consequence: it MISSED the largest deletion in its own window
`6f86ff32a7dbd54e4f2f933a6d6c327be9b04884` "docs(todo): track remaining Stage 4
gates" (2026-08-11 07:17:15) is an ancestor of `origin/main`, sits squarely
inside the audit's window, and:

- reduced the tree from **113,030 files to 3**;
- deleted **113,027 files / 40,222,376 lines**;
- has a single-file deletion of **635,236 lines** — **335× larger** than the
  next-biggest in the window (1,896) and the #1 entry by every threshold the
  audit declared (≥300 total, ≥200 single-file, ≥40 files).

It is not among the 12 flagged commits. It is not a merge (1 parent), and plain
`git log --numstat` *does* emit its 113,027 rows — so the audit's method would
have caught it had the data not been truncated. This is the fourth tree wipe,
tracked separately in
`fourth_tree_wipe_6f86ff32a7d_guard_not_enforced_2026-08-11.md`.

The surviving 3 files were two bug docs and `todo_db.sdn`.

### Defect 3 — a known-in-flight race recorded as a settled verdict
Row 3 was written as **"STILL MISSING"** and ranked #1 under "Still-missing
content requiring restoration", while the same row says *"Another agent is
already restoring this one."* The real history:

```
6e2f613d302  08-10 06:40  5998 -> 4211   the clobber
ad2b5d5307f  08-11 06:00  4211           the "revert" did NOT restore this file
6f86ff32a7d  08-11 07:17  -> 0           tree wipe (audit missed this entirely)
ae55a746719  08-11 07:22  4211           wipe undone, still clobbered
64a4364d36a  08-11 08:14  6012           the ACTUAL restore
```

The audit's observation was true when taken and stale within hours. A
point-in-time measurement of a contested file must carry the commit it was
measured at, or it becomes a false alarm the moment the race resolves — which
is exactly what happened, costing a later reader a full re-verification pass.

### Rules for the next audit
1. **Assert input size before concluding.** Print the row/commit count you
   actually processed and sanity-check it against an independent count. A
   negative finding from an unverified-size dataset is not a finding.
2. **Rank by magnitude and eyeball the top entry.** The largest deletion in the
   window should be row #1 by construction; if the biggest thing in your table
   is 1,896 lines in a repo that wipes 600k, your scan is incomplete.
3. **Timestamp and pin volatile rows.** Record the exact SHA measured at, and
   never write "STILL MISSING" for a file another agent is actively restoring —
   use "in flight, owned by X, re-check at <SHA>".

## No new guard added — the existing one already covers this class
A mass `rt_*` deletion is already gated by
`scripts/check/check-runtime-api-regression-push.shs` (fails at ≥5 removed
symbols, and unconditionally when a removed symbol is still `pub use`-exported
in `lib.rs`). The `rt_*` export surface in `runtime/src/lib.rs` currently
carries 471 references and is healthy. Adding a second export-surface assertion
would duplicate an existing, already-wired guard.

---
*Original audit text below, retained unedited for the record. Its Row 3 verdict,
its 2714-row basis, and its "no new deletions found" summary are all superseded
by the re-verification above.*

# Silent Mass-Deletion Audit — commits landed 2026-08-10 12:00 .. 2026-08-11 (origin/main)

## Scope and method
- Window: `git log --since="2026-08-10 12:00" --format='%H %s' origin/main` → **343 commits**.
- Diffstat for every commit pulled in one pass (`git log --numstat`, 2714 file-change
  rows) and scanned against three thresholds: total deletions ≥ 300 lines, any single
  file losing ≥ 200 lines, or ≥ 40 files changed in one commit.
- **12 commits flagged.** Each was checked: pre-commit line count, post-commit line
  count, and the count of the *same path* at the current origin tip (so a later
  restore is visible), plus symbol-set diffs (`grep -o 'fn ...'`) and the commit body
  for stated rationale.

## Already-known incident — do not double-restore
`6e2f613d302941d0733bf5907355e68de8e9f7f1` ("fix(runtime): preserve u64 across erased
values") is the reported stale-snapshot clobber of
`src/compiler_rust/runtime/src/value/collections.rs` (5998 → 4211 lines, 70 functions
missing, confirmed still missing at origin tip as of this audit). **Another agent is
already restoring this one — do not act on it here.**

## Flagged commits

| # | SHA | Title | Files | Total del | Max single-file del | Verdict | Evidence |
|---|-----|-------|------:|----------:|---------------------:|---------|----------|
| 1 | `ad2b5d5307f` | revert: restore tree wiped by accidental bulk-deletion in 7731b4c139 | 419 | 9067 | 1896 (collections.rs) | **RESTORED-SINCE** (this commit IS the restore) | Landed 06:00:13, one minute after #2; title states purpose |
| 2 | `7731b4c1394` | fix(compiler): dynamic-dispatch `.expect()` ... | 427 | 33446 | 1009 (`directory_fanout_baseline.txt`) | **CLOBBER, but RESTORED-SINCE** | Landed 05:59:10; wiped 427 files broadly under a narrow "fix" title — exactly the innocuous-title/wide-diff shape; reverted 1 minute later by #1. Confirmed: `directory_fanout_baseline.txt` etc. are back at origin tip. |
| 3 | `6e2f613d302` | fix(runtime): preserve u64 across erased values | 34 | 2543 | 1896 (collections.rs) | **CLOBBER — STILL MISSING** (already being handled elsewhere, do not double-restore) | Pre=5998 lines/268 `fn`s, post=4211/198 `fn`s; current origin tip still 4211/198 — 70 functions still absent, e.g. `rt_array_free_deep`, `rt_array_reduce`, `rt_push`, `rt_pop`, `rt_drop`, `rt_find`, `deep_free_classify`, `collection_provider_cache` |
| 4 | `27dcf4ac472` | fix(test): clear the test-tree divergence RED (4 offenders + mockspec reconcile) | 7 | 998 | 590 (`test/01_unit/std/mock_spec.spl`) | **INTENTIONAL** | Body documents dedup of a 593-line near-duplicate reimplementation down to a thin wrapper over `std.spec.mock`, citing `doc/08_tracking/bug/mock_specs_shadow_callrecorder_callverifier_full_reimpl_2026-08-10.md`; twin `test/unit/std/mock_spec.spl` (#11) shrinks identically and consistently |
| 5 | `62494425ed4` | fix(test): make two fake gates measure real drift | 7 | 440 | 219 (`cli_help_alignment_spec.spl`) | **INTENTIONAL** | Net shrink modest (262→254 lines at commit, 277 at current tip — content net grew since); title matches scope |
| 6 | `21315d9aacc` | fix(cli): wire stats/doc-coverage into seed COMMAND_TABLE | 28 | 3447 | 226 (`cipher_sha256_provider.spl`) | **RESTORED-SINCE** | File was fully deleted in this commit (226→0) but is back to 226 lines at current origin tip — a later commit restored it. Off-topic to the stated "wire stats/doc-coverage" scope; worth a follow-up on *why* an unrelated spec file was deleted here, but no longer actionable since it's back. |
| 7 | `e92177f6fe1` | refactor(compiler): remove duplicated logic in front/mid-end | 12 | 3399 | 661 (`simd_phase9c.spl`, deleted) | **INTENTIONAL** | Body documents exhaustive-grep verification of zero importers + byte-identical archive copies for 7 orphan phase files, and byte-identical duplicate-function removal in the interpreter with drifted pairs explicitly left alone and filed; well-evidenced |
| 8 | `5eda4b12ecc` | refactor(browser_engine): delete the dead third CSS color/length lane | 3 | 326 | 182 (`css.spl`) | **INTENTIONAL** | Body documents a measured zero-external-reference dead lane superseded by `dom_color.spl` (strict superset); importer specs shown byte-identical before/after |
| 9 | `be5d8b99df1` | test(type_infer): exercise the real HM engine; RED on two DimSolver defects | 5 | 644 | 322 (`type_infer_correctness_spec.spl`) | **INTENTIONAL** | Small net shrink (353→348, stable at current tip); title states a test-quality rewrite, not a sweep |
| 10 | `ebb2d78719e` | fix(test): convert riscv_dual_arch_spec to describe/it, wire real kernel types | 3 | 478 | 239 (`riscv_dual_arch_spec.spl`) | **INTENTIONAL** | 239→130 lines, stable at current tip; scoped to the named file, matches title |
| 11 | `76caeb0e6ea` | fix(test): rewrite mock_spec.spl twins against real std.spec.mock API | 3 | 996 | 590 (`test/unit/std/mock_spec.spl`) | **INTENTIONAL** | Twin of #4, same dedup rationale, same bug doc |
| 12 | `d6c1ea22797` | test(narrowing): exercise the real narrowing algorithm, not a text mirror | 3 | 560 | 280 (`narrowing_spec.spl`) | **INTENTIONAL** | 421→366 lines, stable at current tip; scoped to the named file |

## Still-missing content requiring restoration (ranked)

1. **`src/compiler_rust/runtime/src/value/collections.rs`** — 70 functions still absent
   at origin tip (commit `6e2f613d302`). **Already being restored by another agent per
   task instructions — do not duplicate this work.**
2. Nothing else from this 12-commit flagged set is still missing: #1/#2 (the 427-file
   sweep) self-corrected within one minute via an explicit revert commit, and #6
   (`cipher_sha256_provider.spl`) was restored by a later, unidentified commit — a
   follow-up item (not urgent) is to identify *which* commit restored #6 and confirm
   it wasn't a coincidental re-add that could itself regress.

## Summary
- Commits scanned: 343 (diffstat rows: 2714)
- Flagged: 12
- Verdict breakdown: 1 CLOBBER (still missing, already owned elsewhere), 2
  CLOBBER-but-RESTORED-SINCE (`7731b4c1394` restored by `ad2b5d5307f`;
  `21315d9aacc`'s deleted file restored by a later commit), 9 INTENTIONAL (all with
  either an accompanying bug doc, exhaustive-grep dead-code evidence, or a stable
  post-commit line count matching the stated scope), 0 UNCLEAR.
- No new, still-unaddressed silent deletions were found beyond the already-reported
  `6e2f613d302941d0733bf5907355e68de8e9f7f1`.
