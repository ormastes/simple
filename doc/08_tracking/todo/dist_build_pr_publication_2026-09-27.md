# Publish an isolated distributed-build review PR

Status: BLOCKED. Priority: P1. Owner: distributed-build merge owner.

The current checkout is detached and contains a large mixed staged worktree.
Do not commit or push that combined state as the distributed-build PR. Prepare
an isolated review checkout from the intended base, apply only the owned
distributed-build files, and retain a path inventory and
diff before committing. Keep the PR a draft while live two-worker execution,
Simple specs, exact-tree process ownership, and fast-push receipt binding
remain incomplete.

2026-09-27 correction: the Mac preflight slice below is a superseded VM
prototype. The user selected native macOS execution and excluded VMs from
Simple Container. Do not apply or publish the Mac preflight patch. Use the
[native Mac plan](../../03_plan/agent_tasks/native_macos_simple_container.md)
for future Mac work; keep the distributed-build PR isolated from it.

On 2026-09-27, both ordinary and `GH_TOKEN`/`GITHUB_TOKEN`-unset
`gh auth status` reported an invalid token for the active `ormastes` account.
Prior GitHub write attempts were also rejected by automatic approval review.
An isolated local branch named `codex/macos-simpleos-preflight-20260927` now
contains the five-path Mac preflight review slice; the review patch is at
`build/handoff/macos-simpleos-preflight-review-2026-09-27.patch`. Its authorized
push failed because this host could not resolve `github.com`. The branch is
local only and no PR exists.
The GitHub connector then rejected branch creation because the action requires
approval and this session's approval policy is `never`. Remote `main` was at
`15d989519be3d4b9b9aeaa3eb627b6bff874110b`, ahead of the local base
`664c80efda56bbb6903e4e427434e755cb430094`; its TODO IDs 338 and 339
already have different owners. Rebase the five-path patch onto the remote tip
and assign a fresh TODO ID before any future push. Do not push the current
local branch as-is.
After GitHub write access is restored, prepare a new distributed-build-only
patch from the current owned files, rebase it onto current `main`, push the
resulting branch, and open the draft PR. Record the PR URL,
head commit, selected path inventory,
test receipts, and outstanding TODO links here. Do not claim the PR is ready to
land until verify reports PASS and platform evidence is attached.

A bounded ten-path review slice from this session is available at
`build/handoff/dist-build-owned-review-2026-09-27.patch`, with its SHA-256,
scope and dependency caveat in the adjacent `.md` handoff. It is not the full
candidate and has not been pushed or run through Simple verification.
