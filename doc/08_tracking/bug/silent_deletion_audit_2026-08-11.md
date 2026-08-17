## Row #3 re-verified 2026-08-17 — RESTORED, close this row

`src/compiler_rust/runtime/src/value/collections.rs` is back at **6148 lines /
210 `fn rt_*`** (audit recorded 4211/198 as still-missing). `rt_array_reduce`
and `rt_array_free_deep` are present. No double-restore needed; the "STILL
MISSING" verdict for `6e2f613d302` is stale.

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
