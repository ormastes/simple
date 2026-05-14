# SPipe Process Harness User Approval Plan

Date: 2026-05-15
Status: awaiting explicit user approval

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
This plan therefore records the approvals needed before regenerating or
recreating SPipe process harness artifacts.

## Recommended Selection

Recommended requirement selection:

- Feature Option 3: shared hook/deploy foundation, goal/SPipe gates, and full
  CLI HUD.
- NFR Option 3: hook-safe behavior, production gate targets, and operational HUD
  targets.

This is only a recommendation. The repo rule requires the user to explicitly
select requirements. A valid approval phrase is:

```text
Approve Feature Option 3 and NFR Option 3 for SPipe process harness.
```

## User Verification Required

The user must confirm these items before implementation starts:

1. Requirement selection:
   - Confirm the exact feature option.
   - Confirm the exact NFR option.
   - Confirm whether unchosen option files should be deleted after final
     requirement docs are written, as required by repo policy.

2. Scope confirmation:
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

3. Design approval:
   - Approve final architecture document.
   - Approve final detail design.
   - Approve TUI/HUD design if the HUD is interactive.
   - Approve system test plan and SPipe spec locations.

4. Verification approval:
   - Confirm acceptable local smoke commands if `bin/simple` is absent.
   - Confirm required hook validation method for Codex, Claude, and Gemini
     configs.
   - Confirm whether live client manual verification is required or whether
     config/rendered-hook tests are enough.

5. VCS approval:
   - Approve committing only SPipe process harness changes.
   - Approve leaving unrelated current `scv` worktree changes untouched.
   - Approve `jj pull --rebase` or repo-local equivalent before push.
   - Approve push target and remote/branch.

## Remaining Work After Approval

1. Recreate research artifacts if absent:
   - `doc/01_research/local/spipe_process_harness.md`
   - `doc/01_research/domain/spipe_process_harness.md`

2. Write selected final requirements:
   - `doc/02_requirements/feature/spipe_process_harness.md`
   - `doc/02_requirements/nfr/spipe_process_harness.md`

3. Remove unchosen option artifacts after final requirement docs exist.

4. Create design artifacts:
   - `doc/04_architecture/spipe_process_harness.md`
   - `doc/05_design/spipe_process_harness.md`
   - `doc/05_design/spipe_process_harness_tui.md`
   - `doc/03_plan/sys_test/spipe_process_harness.md`
   - `doc/03_plan/agent_tasks/spipe_process_harness.md`
   - `doc/06_spec/app/<app_name>/feature/spipe_process_harness_spec.spl`

5. Implement:
   - Common provider hook event model.
   - Codex hook adapter/config deployment.
   - Claude hook adapter/config deployment.
   - Gemini hook adapter/config deployment.
   - Skill deploy/update integration.
   - Per-skill provider hook calls.
   - CLI HUD state collector and renderer.
   - Durable `.spipe/<feature>/state.md` goal state integration.
   - SPipe gate/prevent command.

6. Verify:
   - Unit and integration tests for adapters, deploy/update, HUD, goal state, and
     gates.
   - Config generation tests for Codex, Claude, and Gemini.
   - SPipe quality checks for non-stub tests.
   - Runtime smoke checks available in this workspace.

7. Ship after explicit user approval:
   - Review dirty worktree and separate unrelated changes.
   - Commit SPipe process harness changes.
   - Pull/rebase.
   - Re-run required verification after rebase.
   - Push to the approved remote/branch.

## Approval Phrase Needed

To proceed, the user should reply with:

```text
Approve Feature Option 3 and NFR Option 3. Proceed with the plan doc, keep unrelated scv changes untouched, and ask again before jj commit/rebase/push.
```
