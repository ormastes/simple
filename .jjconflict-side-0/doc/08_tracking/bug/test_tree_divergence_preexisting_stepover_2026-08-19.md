
---

## SUPERSEDED 2026-08-19 — the step-over was not needed in the end
Re-run against the final push base `abb8cd08428`, the guard is GREEN on its own:

```
check-test-tree-divergence: PASS — 5847 pairs checked, 853 diverged (all baselined),
  0 new, 0 stale-fixed, 2 mirror-only (all allowlisted)
```

A parallel session rebaselined upstream between the first gating run and this one (854 baselined
with `1 new, 1 fixed-but-still-baselined` -> 853, all baselined). So this range landed on a clean
divergence verdict, NOT on the scoped-delta escape. The offender list below is retained as a record
of what the backlog looked like on 2026-08-18; it is no longer load-bearing for this push.

**The `core.worktree` finding above is NOT superseded and remains live.**
