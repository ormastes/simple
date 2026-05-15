# SPipe Process Harness User Approval Plan

Date: 2026-05-15
Status: approved and implemented

## Objective

Build a production-level SPipe process harness that provides shared hook
infrastructure for Codex, Claude, and Gemini; deploy/update infrastructure for
skills; per-skill hook integration for the three LLM clients; a CLI HUD showing
model, jj worktree, commit, hours remaining, and week remaining; and a durable
goal/SPipe gate that can prevent unsafe progress.

## Current Workspace Finding

The current workspace does not contain the previously referenced
`spipe_process_harness_*` research, requirement, state, or completion-audit
artifacts. The current dirty worktree contains unrelated `scv` feature changes.
This plan records the approval and tracks the regenerated SPipe process harness
artifacts.

## Recommended Selection

Recommended requirement selection:

- Feature Option 3: shared hook/deploy foundation, goal/SPipe gates, and full
  CLI HUD.
- NFR Option 3: hook-safe behavior, production gate targets, and operational HUD
  targets.

The user selected full scope on 2026-05-15 with:

```text
do full scope and update plan and jj commit pull rebase and push
```

## User Verification Required

Completed user confirmations:

1. Requirement selection: full shared hook/deploy/HUD/prevention scope.
2. VCS action: commit, pull/rebase, and push after verification.
3. Safety boundary: keep unrelated `scv` worktree changes untouched.

Implementation scope:
   - Common hook infra must target Codex, Claude, and Gemini.
   - Hook behavior must preserve raw provider payloads for debugging and replay.
   - Hook behavior must normalize provider events into one internal contract.
   - Hooks should report failures consistently even where provider blocking
     semantics differ.
   - Skill deploy/update infrastructure must install or update provider-specific
     hook config for all three LLM clients.
   - Each skill invocation should call the common infra for Codex, Claude, and
     Gemini.
   - CLI HUD must include model, jj worktree, commit, hours remaining, and week
     remaining.
   - Durable goal/SPipe state must exist outside live Codex session memory.
   - The SPipe prevent/gate mechanism must block or fail progress when required
     state, checks, or approvals are missing.

## Remaining Work

1. Created research artifacts:
   - `doc/01_research/local/spipe_process_harness.md`
   - `doc/01_research/domain/spipe_process_harness.md`

2. Created selected final requirements:
   - `doc/02_requirements/feature/spipe_process_harness.md`
   - `doc/02_requirements/nfr/spipe_process_harness.md`

3. No unchosen option artifacts existed in this workspace.

4. Created design artifacts:
   - `doc/04_architecture/spipe_process_harness.md`
   - `doc/05_design/spipe_process_harness.md`
   - `doc/05_design/spipe_process_harness_tui.md`
   - `doc/03_plan/sys_test/spipe_process_harness.md`
   - `doc/03_plan/agent_tasks/spipe_process_harness.md`
   - `doc/06_spec/app/<app_name>/feature/spipe_process_harness_spec.spl`

5. Implemented:
   - Common provider hook event model.
   - Codex hook adapter/config deployment.
   - Claude hook adapter/config deployment.
   - Gemini hook adapter/config deployment.
   - Skill deploy/update integration.
   - Per-skill provider hook calls.
   - CLI HUD state collector and renderer.
   - Durable `.spipe/<feature>/state.md` goal state integration.
   - SPipe gate/prevent command.

6. Verification:
   - Unit and integration tests for adapters, deploy/update, HUD, goal state, and
     gates.
   - Config generation tests for Codex, Claude, and Gemini.
   - SPipe quality checks for non-stub tests.
   - Runtime smoke checks available in this workspace.

7. Ship:
   - Review dirty worktree and separate unrelated changes.
   - Commit SPipe process harness changes.
   - Pull/rebase.
   - Re-run required verification after rebase.
   - Push to the approved remote/branch.

## Approval State

No further user approval is needed for this requested scope. The remaining VCS
work must still avoid committing unrelated `scv` changes.
