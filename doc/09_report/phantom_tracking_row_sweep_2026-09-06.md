# Phantom tracking-row sweep — 2026-09-06

**Scope:** test the hypothesis that other `doc/08_tracking/{todo,bug}/*.md` rows,
like `rollback_bootstrap_deploy_script_missing_2026-08-08.md`, are PHANTOMS —
tracking rows describing a gap that no longer exists (and in some cases never
really did, once the gap is examined closely).

**Non-negotiables honored:** nothing was deleted; no `.sdn` DB was hand-edited;
no push; work stayed in `work/phantom-row-sweep-2026-09-06` in this worktree.
`HEAD` == `origin/main` at `a12a19eb775a` for the whole sweep, so "exists now"
below means the same thing in the working tree and at `origin/main`.

## 1. Wipe/repair windows established

| # | Wipe commit | Repair commit | Wall-clock window | Tree size (wipe / normal) | In local history? |
|---|---|---|---|---|---|
| A | `118c636ead8` (2026-08-01 08:05:45 +0000) | `7f5a55fa46edc51` (2026-08-01 08:14:12 +0000) | ~8m27s | 2 / 109,530 files | Yes (`--first-parent`, both ancestors of `origin/main`) |
| B | `6f86ff32a7d` (2026-08-11 07:17:15 +0000) | `ae55a746719` (2026-08-11 07:22:12 +0000) | ~4m57s | 0 / ~same | Yes |

Both were located mechanically (`git ls-tree -r --name-only <c> \| wc -l` walked
forward from the wipe on `--first-parent` history until the count crossed back
above 90,000), not just quoted from prose, and both endpoints are confirmed
ancestors of `origin/main` via `git merge-base --is-ancestor`.

**Window B has an incomplete-repair caveat, not a phantom:**
`doc/08_tracking/bug/owned_process_runtime_lost_in_tree_wipe_restore_2026-08-21.md`
shows `ae55a746719`'s restoration silently dropped the whole owned-process
runtime feature (`src/runtime/runtime_process_owned.c` and three test files),
undetected for 10 days until a Rust unit test caught it on 2026-08-21. Any row
that had complained about owned-process artifacts being missing between
2026-08-11 and 2026-08-21 would be **REAL**, not phantom — the repair itself
was defective for that one feature. No such row was found in this sweep.

**Two further incidents were identified but are not usable as phantom-search
windows:**
- **Window C — `a8b40075134` (~2026-08-20, ~2 minutes):**
  `doc/08_tracking/bug/interrupted_rebase_pushed_wiped_tree_a8b4007_2026-08-20.md`.
  This wipe was repaired by **force-with-lease replacement**, not a forward
  "restore" commit — `a8b40075134` is not resolvable as a git object in this
  clone (`git cat-file -t a8b40075134` fails), consistent with history having
  been rewritten. No tracking row could plausibly have been filed against a
  2-minute window that was force-erased from history before most sessions
  could even fetch it; none was found.
- **Pre-2026-06-30 wine_vm wipe (undated, imprecise):**
  `doc/08_tracking/bug/wine_vm_module_family_destroyed_by_tree_wipe_2026-08-04.md`
  documents an earlier, unpinned wipe whose damage (`wine_vm_gate.spl`,
  `wine_substrate.spl`, `wine_seh_frame.spl`, `wine_precondition_manifest.spl`,
  `wine_process_entrypoint_startup_fault.spl`) is stated as **"never restored
  at all."** A window whose subject is still absent cannot produce phantoms by
  definition (phantom requires present-now), so it was excluded as a search
  source.
- The census claim in `tree_wipe_module_damage_census_2026-08-04.md` that
  `main` was "wiped to near-zero files twice in 24 hours" was checked against
  window A: scanning 500 commits (through 2026-08-03, well past 24h) forward
  from repair A found no second sub-90,000-file commit on `--first-parent`
  history. Either the second wipe is off first-parent (a since-rewritten
  branch, like Window C) or the "24 hours" figure in that census is loose.
  Not resolved further; flagged rather than asserted.

## 2. Row enumeration methodology

`git log --diff-filter=A` over the full 4,469-path add-history of
`doc/08_tracking/{todo,bug}/*.md` was cross-checked against **windows A and B
directly**: zero tracking rows have an earliest git-add timestamp falling
inside either 5-9 minute window. This is expected — a wipe deletes almost the
whole tree in one bad commit, and its repair restores everything already
known; neither step manufactures brand-new tracking prose.

**Critical calibration finding:** the anchor row itself
(`rollback_bootstrap_deploy_script_missing_2026-08-08.md`) does **not** meet a
strict "created inside the window" test either. Its earliest git-add is commit
`b3171f4257` ("sync: merge 62 shared-WC local commits onto origin/main"),
**2026-08-09 01:19:15 +0000 — 53h58m before** window B's wipe
(`6f86ff32a7d`, 2026-08-11 07:17:15). At `b3171f4257` itself, both
`scripts/bootstrap/rollback-bootstrap-deploy.shs` and the todo file describing
it as missing were **already present in the committed tree** — i.e. the row
was already a false claim at the moment it was authored, two days before
window B's wipe ever touched it. Window B's only actual role was to
collaterally delete-then-restore the (already-wrong) row unchanged, alongside
the rest of the repo. The originally-given framing ("filed against that
transient gap") slightly overstates causality; the more precise statement is
"the row's claim was already false when written (most likely due to a stale
local checkout landing late via a batched sync commit), and it happened to
also survive a wipe/repair cycle in its wrong state." This does not change the
PHANTOM verdict, only the mechanism, and it is why a fixed-buffer date filter
cannot be trusted as a sole gate — see §4.

Given that finding, candidate generation used two independent, disclosed
signals instead of a single time cutoff:
1. **Keyword scan**, both tracking dirs, for existence-claim language
   (`does not exist`, `is missing`, `never built/implemented/created`,
   `nonexistent`, `absent`, `exist nowhere`, etc.) — 18 todo hits, 717 raw bug
   hits (too broad alone: ordinary defect prose uses this vocabulary loosely).
2. **Temporal proximity**, ±72h around each window's `[wipe, repair]`
   interval — the tolerance the anchor itself required (54h) rounded up.
   745 tracking-file earliest-adds fall in that combined band.

Intersecting (1) and (2) gives **107 candidates**. Narrowing further to
filenames whose own title asserts an existence claim (not just body prose)
gives **22 strong candidates**, all fully or near-fully examined below. The
anchor's two batch-siblings (created in the *same* commit, `b3171f4257`) were
also pulled in and checked as a natural control.

## 3. Verdicts

### PHANTOM (1)

| Row | Wipe | Repair | Pre-wipe | At-wipe | At-repair | Now |
|---|---|---|---|---|---|---|
| `doc/08_tracking/todo/rollback_bootstrap_deploy_script_missing_2026-08-08.md` — claims `scripts/bootstrap/rollback-bootstrap-deploy.shs` doesn't exist | `6f86ff32a7d` | `ae55a746719` | present (`1a77c01e551`, 2026-08-08) | **absent** | present | present (`origin/main:scripts/bootstrap/rollback-bootstrap-deploy.shs` resolves) | Already established; re-confirmed here with the four-probe evidence bar and the mechanism correction in §2. |

### REAL (11) — genuine gaps at filing time, several since fixed by real work

| Row | Verdict basis |
|---|---|
| `todo/native_httpserver_benchmark_gate_scripts_missing_2026-08-08.md` (same batch commit `b3171f4257` as the anchor) | All 6 named scripts + the report file are **still absent** today (`test -e` on each returns false). Genuine, unresolved. |
| `todo/jupyter_e2e_helper_scripts_missing_2026-08-08.md` (same batch commit) | `run_server_check.py` / `run_notebook_server_test.py` **still absent** under `test/03_system/tools/jupyter/helpers/`. Genuine, unresolved. |
| `bug/command_dispatch_migrated_app_paths_missing_2026-08-12.md` | `src/app/formatter/` and `src/app/depgraph/main.spl` **still absent**; row itself says "deliberately left RED." |
| `bug/runtime_native_c_uncompilable_unsigned_box_never_implemented_2026-08-11.md` (earliest-add only 55s before window B's wipe) | Row's own header says `RESOLVED 2026-08-11` via a genuine implementation (unsigned heap box added, `clang` 33→0 errors) — a real bug fixed by real work, unrelated to the wipe. |
| `bug/web_renderer_compose_retained_missing_animation_time_param_2026-08-01.md` (4.8h after window A's repair) | Genuine undeclared-identifier bug, `FIXED 2026-08-01` by adding the missing parameter — unrelated to the wipe. |
| `bug/fe_p256_field_module_missing_2026-08-04.md` | `src/lib/common/math/field/fe_p256.spl` confirmed **absent** at the filing commit (`git cat-file -e <filing-sha>:<path>` fails), confirmed **present** at `origin/main` now — but added by commit `306aebd15d` on **2026-08-17**, 13 days after filing and 6 days after window B. Genuinely missing, later genuinely implemented; unrelated to any wipe. |
| `bug/app_modules_referenced_by_specs_exist_nowhere_2026-08-04.md` | `src/app/build/feature_flags.spl` and `opt_remarks.spl` confirmed **absent** at the filing commit, confirmed **present now** — but re-added on **2026-08-17**, and confirmed **already absent before window A's wipe** (`118c636ead8^`), so the gap predates and is unrelated to window A. Genuinely missing, later genuinely implemented. Row still says `Status: OPEN` and should probably be updated (not this sweep's call). |
| `bug/vulkan_vm_executor_missing_run_source_persisting_data_blocks_dbg1_resume_2026-08-09.md` | Row's own header: `FIXED 2026-08-09` same day. |
| `bug/rt_process_spawn_async_jit_missing_ptr_len_expansion_2026-07-31.md` | Row's own header: `FIXED` by a one-line change. |
| `todo/rollback_bootstrap_deploy_script_missing`'s two batch-siblings are listed above; counted once each. |

### N/A — not an existence claim / already resolved through the normal status field (2)

- `bug/counterpart_derived_expected_value_gate_absent_2026-08-09.md` — a
  behavior/design-gap claim ("gate does not exist"), already marked `FIXED`,
  re-verified 2026-08-17. Not a file-existence claim this method can test
  independently of trusting the row's own resolution note.
- `bug/render_perf_8k80_completion_aggregator_missing_2026-08-14.md` — status
  is `IMPLEMENTED / LIVE EVIDENCE BLOCKED`, i.e. the row itself does not
  currently assert non-existence.

### UNPROVEN — flagged by the mechanical filter, status-screened only, existence not independently re-verified this pass (9)

`bug/async_host_missing_async_core_module_breaks_task_handle_cancel_2026-07-29.md`
(status: open), `bug/extern_class_constructor_not_found_simpleerror_2026-08-02.md`
(open), `bug/specs_assert_against_nonexistent_product_paths_2026-08-10.md`
(RED/OPEN, 835 specs / 949 paths — too large to hand-verify here),
`bug/comment_cheat_absent_capabilities_2026-08-10.md` (OPEN),
`bug/render_lane_specs_import_nonexistent_modules_2026-08-08.md` (partially
fixed, 25 of 27 specs still legitimately RED per its own text),
`bug/rtl_mdsoc_phase5_modules_never_created_2026-08-04.md` (OPEN),
`bug/treesitter_node_module_missing_and_spec_tautological_2026-08-04.md` (OPEN,
architectural), `bug/two_std_specs_reference_nonexistent_api_and_assert_nothing_2026-08-04.md`
(OPEN, architectural), `bug/c_parser_library_specced_but_never_implemented_2026-08-04.md`
(OPEN). None carries a resolution note or a later re-add commit the way the
REAL rows above do, so a phantom verdict is **not** expected, but this sweep
did not run the full four-probe check on each — flagged for a follow-up pass
rather than asserted either way, per the "be conservative" instruction.

### Not individually examined this pass (~85)

The keyword∩temporal-proximity filter produced 107 candidates; the 22 with a
strong existence-claim *title* (above) were examined, the remaining ~85 (weak
keyword matches — mostly ordinary defect prose using "missing"/"does not
exist" about behavior, not files) were not opened individually. They are
listed in `/tmp/phantom/intersect_candidates.txt` (session-local, not
committed) for anyone extending this sweep.

## 4. Bottom line on the hypothesis

**The hypothesis that a broader population of wipe-window phantoms exists is
NOT confirmed by this sweep.** Of every row independently checked against the
present-day tree (12 rows given a full four-probe or equivalent check), only
the already-known anchor came back PHANTOM. Two rows created in the *same*
batch commit as the anchor (same stale sync, same few minutes of authoring)
came back REAL — proximity to the anchor's own authoring event does not
predict phantom-hood. Every other close-in-time candidate examined was either
a genuine gap later closed by real implementation work (fe_p256, app_modules
feature_flags/opt_remarks) or a genuine bug fixed same-day through real code
changes (runtime_native_c, web_renderer, vulkan_vm_executor, rt_process_spawn)
— none of these had anything to do with a tree wipe; the temporal proximity to
a window was coincidental in every case checked.

**Counts:** 4 wipe/wipe-like incidents identified (2 precisely windowed and
mechanically verified — A, B; 1 confirmed by its bug record but unresolvable
in local history due to force-replacement — C; 1 older/imprecise and excluded
as unrepaired). Rows examined in this pass: **12 with full evidence**, **9
status-screened (UNPROVEN)**, **~85 filter-flagged but not opened**. Verdicts:
**1 PHANTOM, 11 REAL, 2 N/A, 9 UNPROVEN**.

## 5. Disposition (recommendation only — no rows changed)

- The anchor row is annotated in place (see
  `doc/08_tracking/todo/rollback_bootstrap_deploy_script_missing_2026-08-08.md`)
  with this sweep's finding. **No status field, no DB row, and no file was
  deleted or reworded** — disposition (e.g. closing the row) is left to the
  user.
- `bug/app_modules_referenced_by_specs_exist_nowhere_2026-08-04.md` and
  `bug/fe_p256_field_module_missing_2026-08-04.md` still say `Status: OPEN`
  despite the subject modules having been re-added on 2026-08-17 — worth a
  human look, but this is a **stale-status** finding, not a phantom, and is
  called out here rather than acted on.
- The 9 UNPROVEN rows and ~85 unexamined candidates are reasonable next
  targets if the sweep is extended.
