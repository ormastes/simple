# SimpleOS lane survey 2026-09-18 — ~70 lanes stalled mid-plan; preservation + resume map

**Date:** 2026-09-18
**Scope:** all September SimpleOS worktrees (`/tmp/simpleos-*`, `/home/yoon/dev/simpleos-*`) and branches (`work/simpleos-*`, `codex/simpleos-*`, `lane/*`)
**Verdict:** NOT DONE — the shared SimpleOS body of work stalled mid-plan in two abrupt waves and none of it reached main.

## Hard numbers

- ~70 worktree lanes; **0** tips are ancestors of `origin/main`; **0** are
  patch-superseded (`git log --cherry-pick --right-only` + subject greps for
  the 5 key tips all return 100% unsuperseded commits); **0** open SimpleOS PRs.
- **No live processes** on any SimpleOS worktree (all codex/claude sessions
  run in the main checkout).
- Authoritative plan doc
  `doc/03_plan/agent_tasks/simpleos_production_master_plan_completion_status.md`
  last refreshed 2026-09-05; no plan doc exists for the 09-13..15 wave.

## The two waves (both look like session kills, not completion)

1. **Scheduler identity/exit family** — 7 lanes (`work/simpleos-scheduler-contract`,
   `work/simpleos-control-execution`, `work/simpleos-external-freshness-design`,
   `work/simpleos-scheduler-exit-cleanup`, `work/simpleos-scheduler-terminal-exclusion-v1`,
   `lane/aarch64-target-identity`, `codex/simpleos-pid1-managed-child-binding`),
   152–171 commits each, all stopped between **23:01 and 23:50 on 09-14**.
2. **Storage-pair / dispatch / guest-material wave** — 5 lanes
   (`work/guest-retained-storage-pair-20260915` 306 ahead,
   `work/astra-guest-material-activation-20260915` 302,
   `work/simpleos-canonical-target-provider-20260915` 301,
   `/tmp/simpleos-ordinary-compile-dispatch-20260915` 306,
   `/tmp/simpleos-stdio-cleanup-astra-20260915` 255), stopped between
   **12:00 and 12:56 on 09-15**. Two worktrees
   (`/tmp/simpleos-key-manifest-provision.7GfYi7`,
   `/tmp/simpleos-nvme-reset-io-exclusion-astra-20260915`) were left **dirty at
   the same tip `ea1080a6bf0`** ("retain authenticated guest storage pair
   custody prerequisite").

Plus the older strata: the 09-14 morning physical-release cut-set family
(~20 lanes sharing a base, ahead 51–142, whose receipt lane
`work/simpleos-release-cutset-20260914` defined the cut-set but never landed
receipts) and the 09-13 codex manifest/cli family.

## Why nothing was force-landed

The storage-pair cluster: merge-base 2026-09-13; main has since moved
**480 commits**; the lane has 310, touching 107 `src/compiler` + 79 `src/lib`
files. Rebase = conflict storm (skip); merge-PR = 310 commits over 4 days of
main divergence with likely semantic breakage in shared trees. This needs the
owner lane with a landing strategy (per-family merge PRs in dependency order,
starting from the release-cutset receipt lane), not a drive-by.

## Preservation (done 2026-09-18)

Artifacts captured under `.simple/lane-preserves/` (gitignored, local to this
machine):

- `*.dirty.patch` — uncommitted work from the 3 dirty worktrees
  (key-manifest-provision 19.6KB, nvme-reset-io-exclusion 28.2KB,
  storage-attach-reboot-lineage 4.2KB)
- `*.stash{0,1,2}.patch` — all 3 stashes from each of those worktrees
- `branch-*.mbox` — full email-format patch series of the 3 newest branches
  (~14MB each)

If the `/tmp` worktrees get cleaned, these patches plus the local branches
(`work/*`, `lane/*`) are the recovery path.

## Resume map (highest value first)

1. **Storage-pair cluster** (`ea1080a6bf0` family) — newest work in the repo,
   interrupted mid-lane; dirty state preserved above.
2. **09-15 12:00–12:37 dispatch/material wave** (~300 commits each).
3. **Scheduler identity/exit family** (7 lanes, stopped within one hour —
   likely a shared blocker; investigate that first).
4. **Physical-release cut-set family** (~20 lanes) — land via
   `work/simpleos-release-cutset-20260914` in receipt order.
5. `lane/workspace-namespace-cleanup-20260915` (289 ahead, alone, recent).

## Related note

`json_logic` was surveyed as a possible "simple logics" lane: it is DONE
(doc `json_logic_spec_blocked_stub_modules_2026-06-26.md` closed 2026-09-13);
no lane named "logics" exists in the repo.

## Correction 2026-09-18 (evening) — trial merge measured, revival prepared, vehicle rejected by policy

The "skip" verdict above was re-examined with an actual 3-way merge of the
storage-pair cluster (`ea1080a6bf0`) into current main:

- **Only 10 conflicting files** (5 code: sdn parser 2 hunks, 4 cli/app 1
  hunk each; 5 docs) against 480 commits of divergence — the merge is far
  cheaper than the rebase estimate above.
- All 10 resolved (sdn parser keeps the lane's seq-dispatch walker — it
  passes both sides' pinned specs where a naive HEAD-combination fails the
  lane's strict-traversal spec; cli keeps HEAD's beta.11 version literals;
  docs unioned; todo_db merged 385 rows, 0 duplicate ids).
- The lane's inherent DEPTAIL regression (`cannot iterate over this type:
  Nil`, cost spec 9/11 even on the untouched lane tip — a strong hint why
  the lane stalled) was root-caused and fixed: two main-era Nil-init
  omissions in `module_surface_declarations.spl` (friends/internal_exports
  never projected; ModuleSurfaceField.visibility never passed) that the
  lane's member-visibility code is the first to read. +15 lines.
- Validation after resolution+fix: cost spec 11/11, memo 7/7, owner_index
  4/4, sdn dup-key 3/3, os boot capacity guard 3/3.

**Vehicle rejected by repo policy:** the push gate `push-conflict-tree`
refuses the 311-commit merge ("outgoing commit union ... exceeds its
bounded history limit") — the project enforces linear/rebased history, so
big-merge revival PRs are not landable by construction.

**Preserved for the owner** (in `.simple/lane-preserves/`):
`storage-pair-merged-vs-main.patch` (191k lines, the fully-resolved+fixed
tree vs main), merged tip `7a8661c3e17`. Owner landing path: replay/linearize
per lane (jj-based) using this resolved tree as the conflict-resolution
reference, in dependency order starting from the release-cutset receipt lane.
