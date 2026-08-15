# Test-tree divergence: recorded pre-existing step-over (2026-08-15)

Landing of the engine2d GPU-offload commit used the mechanical delta escape:
`check-test-tree-divergence-delta.shs origin/main <NEW>` = PASS — 16
pre-existing offender(s), 0 introduced by this range. Offender list (verbatim
guard output) recorded alongside as
`test_tree_divergence_preexisting_offenders_2026-08-15.txt` per the vcs rule
that an unrecorded step-over is a violation even with a clean delta.
