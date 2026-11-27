# SCV inventory: untracked-walk budget (2026-11-03)

Bug: `windows_scv_inventory_cold_init_untracked_walk_slow_2026-09-13`.

## Finding
The 2026-09-13 premise (cold-init `ls-files --others` = 47 s) no longer holds.
Remeasured 2026-11-03, full checkout, git for Windows, `--no-optional-locks`:
`ls-files --cached -- src` 0.6 s; `ls-files --others --exclude-standard -- src` 3.5 s.
The remaining cold-init cost (about 935 s, 2 GB) is per-file read + digest, tracked in
`scv_inventory_cold_rescan_935s_per_tree_change_2026-09-26`, not the git walk.

## Design
1. Keep the single `ls-files -t --cached --others` call: it gives tracked and untracked
   membership from one enumeration (consistent cursor). Splitting it (candidate 3) saves
   nothing now and risks inconsistent membership.
2. Replace the hiding 300 s subprocess bound with a named bound
   (`compiler_inventory_git_bound_ms_v1`, 120 s, ~25x margin) so a real regression fails
   in 2 minutes, not 5.
3. Guard: `inventory_git_walk_budget_spec.spl` asserts the bound and a 60 s wall budget
   for the cold-init listing on the live checkout.

Not done (still open, in the 935 s bug): journal-driven untracked discovery, per-path git
blob id caching.
