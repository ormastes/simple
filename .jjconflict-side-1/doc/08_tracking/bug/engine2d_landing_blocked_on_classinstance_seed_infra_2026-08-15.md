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
Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).
Status: OPEN — do not push until unblocked.

## 2026-08-17 re-verification — UNBLOCKED: unblock condition (a) is now satisfied

The blocking prerequisite has landed. `Value::ClassInstance` now exists on
`origin/main`:

```
$ git grep -n ClassInstance origin/main -- src/compiler_rust/compiler/src/value.rs
origin/main:...:1114:pub struct ClassInstance {
origin/main:...:1240:    ClassInstance(Arc<ClassInstance>),
origin/main:...:1346:    Value::ClassInstance(Arc::new(ClassInstance::new(class, fields)))
origin/main:...:1353:    Value::ClassInstance(instance) => Some(instance.class()),
origin/main:...:1361:    Value::ClassInstance(instance) => instance.field(name),
```

So the seed-build guard's stated cause — "Origin's seed has no ClassInstance
variant, so the commit is unbuildable at origin" — no longer holds, and option
(b) (bundling `5958de7d4c7`'s interpreter/value changes) is no longer needed.

The engine2d landing itself is still **not** on origin: `e210ff2af19`,
`d0e976ffef4`, `5958de7d4c7` and `0b894cd7eef` are all `not-on-origin` by
`git merge-base --is-ancestor`. The holding worktree `/mnt/data/tmp/land-wt`
does still exist.

Next action belongs to the engine2d owner, not this triage lane (landing means
pushing, which is out of scope here): re-cherry-pick `e210ff2af19` onto the
current `origin/main`, re-run the full pre-push guard set — the seed-build guard
should now PASS — and land via `sh scripts/check/land.shs`. Re-record the
divergence delta-escape offender list at that time; the one saved at
`/mnt/data/tmp/test_tree_divergence_preexisting.txt` is from 2026-08-15 and is
stale for a fresh range. The separately-noted pre-existing origin red in
`backend_software_damage_spec` is unrelated to this blocker and stays open.

## 2026-08-17 RESOLVED — by supersession, not by landing e210ff2af19

Per-file blob comparison of all 40 files in `e210ff2af19` against
`origin/main` (`git rev-parse <rev>:<path>`, three-way: parent / e210 / origin):

- **31 of 40 files are byte-identical at origin to e210's version.** The work
  landed through another route; re-applying e210 would be a no-op for these.
- **9 files diverge, and origin is strictly FORWARD of e210 in every one**
  (measured as `git diff --numstat`): origin vs e210's *parent* is a large
  add (e.g. `engine2d_web_gpu_offload_spec.spl` +293/-0,
  `node_exec.rs` +489/-18), while origin vs *e210* is a small delta
  (+3/-3 and +169/-17 respectively). Origin contains e210's content plus more.

Spot-verified that the actual fixes are present at origin, not lost:
- `node_exec.rs`: the nested/augmented field-assign diagnostic
  ("cannot assign field on non-object value") is present (3 hits).
- `engine2d_vulkan_cpu_render_diff_spec.spl`: e210 carried a *tolerance*
  (`expect(mism <= 6)`) for the thick-line row-coverage divergence; origin has
  `expect(mism).to_equal(0)` at all three sites — the underlying divergence was
  fixed and the tolerance correctly deleted. Re-applying e210 here would have
  been a **regression**, re-introducing a weakened assertion.
- `backend_software.spl`: e210's offset-loop thick-line implementation was
  replaced at origin by a different (single-guard `sw_bresenham`) path.

Conclusion: **no landing is warranted.** `e210ff2af19` is fully superseded;
applying it verbatim would revert at least one assertion and one implementation.
Nothing was re-applied and no code was changed by this pass.

Status: RESOLVED (superseded at origin). The `/mnt/data/tmp/land-wt` worktree
and commit `e210ff2af19` can be discarded.
