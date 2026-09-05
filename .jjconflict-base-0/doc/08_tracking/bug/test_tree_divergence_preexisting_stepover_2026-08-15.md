# Test-tree divergence: recorded pre-existing step-over (2026-08-15)

Landing of the engine2d GPU-offload commit used the mechanical delta escape:
`check-test-tree-divergence-delta.shs origin/main <NEW>` = PASS — 16
pre-existing offender(s), 0 introduced by this range. Offender list (verbatim
guard output) recorded alongside as
`test_tree_divergence_preexisting_offenders_2026-08-15.txt` per the vcs rule
that an unrecorded step-over is a violation even with a clean delta.


## 2026-08-17 closure

CLOSED — not a defect. This file is the *record* the vcs rule requires when a
landing uses the mechanical delta escape, and it has already served that
purpose. The referenced offender list is present at
`doc/08_tracking/bug/test_tree_divergence_preexisting_offenders_2026-08-15.txt`
(verified on disk 2026-08-17), so the step-over is documented rather than
silent, which is exactly the rule's requirement. No code change is possible or
needed. The underlying test-tree divergence backlog is tracked separately and
is not this record.
