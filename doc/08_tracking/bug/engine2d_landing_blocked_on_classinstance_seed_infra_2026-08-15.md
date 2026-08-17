# engine2d GPU-offload landing blocked on ClassInstance seed infra (2026-08-15)

## Summary
Landing commit e210ff2af19 (cleaned cherry-pick of d0e976ffef4 onto origin/main,
held in /mnt/data/tmp/land-wt) passes 6/7 pre-push guards and all engine2d specs
on the local seed (matrix 16/16, vulkan-vs-cpu render diff 4/4, web offload 9/9,
runtime queue 4/4). The seed-build guard FAILs: node_exec.rs's interpreter fixes
(nested + augmented field assignment on ClassInstance receivers) reference
Value::ClassInstance, which exists only in unpushed local commits owned by the
Stage-4/enhancement session (5958de7d4c7, 0b894cd7eef). Origin's seed has no
ClassInstance variant, so the commit is unbuildable at origin.

## Unblock condition
Either (a) the owning session lands the ClassInstance seed infrastructure on
origin/main — then re-cherry-pick e210ff2af19 (or d0e976ffef4) and push; or
(b) explicit approval to bundle 5958de7d4c7's interpreter/value changes.

## Evidence
- Guard table + logs: session scratchpad {seed-builds,delta,...}.log
- Divergence delta-escape offender list: /mnt/data/tmp/test_tree_divergence_preexisting.txt
  (16 pre-existing, 0 introduced by this range)
- Pre-existing origin red found during verification: backend_software_damage_spec
  "vertically merges every separated run from the prior row" fails on pristine
  origin lib (expected [0,0,64,128,128,0,64,128], got [0,0,256,128]).
Status: OPEN — do not push until unblocked.
