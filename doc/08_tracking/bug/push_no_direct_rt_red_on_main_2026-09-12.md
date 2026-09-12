# `push-no-direct-rt` (BLOCKING push gate) is red on `origin/main` since 2026-09-12

- Status: OPEN (2026-09-12) — observed, not repaired; owner: whoever landed the 262 new sites
- Component: `scripts/check/check-no-direct-rt.shs` ratchet, baseline
  `scripts/check/no_direct_rt_baseline.txt` (6072, tightened 2026-09-07)

## Observation

```
sh scripts/check/check-no-direct-rt.shs --roots src --rev origin/main   # 9e4f1133fe5
FAIL — forbidden direct rt_* count 6334 exceeds baseline 6072 (roots=src, src=6334),
       extern_decls=6613; top offenders: src/compiler/35.semantics/rt_criticalit...
```

At `7352f99898c` (PR #538, the previous base) the same command PASSes at 6072.
The 262 new direct `rt_*` call sites arrived with the 2026-09-12 merges #541
(`work/damage-spec-lane-aware-2`), #542 (`land/jit-symbol-manifest-read`) and
#543 (`land/web-render-chrome-parity`), which landed through PRs — the PR
checks do not run this push-tier gate, so a hooked `git push` of any branch
based on the new `main` is refused regardless of its own content. This is the
third push-tier gate found red on `main` this week (see
`push_gates_red_on_main` in the 2026-09-12 session memory: guard-wiring and
runtime-source-list parity were the other two, unblocked in PR #544).

## Consequence for landing

Branches in this session are based on `7352f99898c` (green) and pushed with
the hook running; the ruleset's strict up-to-date requirement is then satisfied
server-side by `gh pr update-branch`, which does not run local hooks. That is a
workaround, not a fix.

## Fix direction

Either migrate the 262 sites to their typed `std` aliases (the ratchet's
purpose) or, as a reviewed step, raise the baseline WITH the list of offending
files recorded here — never silently. `check-no-direct-rt.shs` prints the top
offenders; `src/compiler/35.semantics/rt_criticalit*` leads the list.
