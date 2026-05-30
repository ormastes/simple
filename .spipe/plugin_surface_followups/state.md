# Feature: plugin-surface-followups

## Raw Request
New task: Work in /home/ormastes/dev/pub/simple on tracker doc/08_tracking/feature_request/plugin_surface_followups.md, especially FR-PLUG-0004 if actionable. You are not alone in the codebase: do not revert others' edits. Own only plugin surface files/tests/docs plus .spipe/plugin_surface_followups/** and tracker. Use $sp_dev workflow. Keep implementation pure Simple where possible; Rust is seed/tooling. Implement or verify next concrete open follow-up, update per-item tracker status. Report changed paths, tests, blockers.

## Task Type
todo

## Refined Goal
Implement or verify the next concrete open plugin-surface follow-up from `plugin_surface_followups.md`, prioritizing FR-PLUG-0004, within the scoped plugin surface files and tracker.

## Acceptance Criteria
- AC-1: The tracker item selected for work has its current status verified from the codebase before implementation.
- AC-2: If FR-PLUG-0004 is actionable within the allowed scope, its next concrete implementation or verification step is completed.
- AC-3: Relevant plugin surface tests or focused checks are run and their results are recorded.
- AC-4: `doc/08_tracking/feature_request/plugin_surface_followups.md` is updated with per-item status for the selected follow-up.
- AC-5: No files outside plugin surface files/tests/docs, `.spipe/plugin_surface_followups/**`, and the tracker are intentionally modified.

## Scope Exclusions
Rust runtime or native backend implementation is out of scope unless needed only for seed/tooling verification.

## Phase
dev-done

## Log
- dev: Created state file with 5 acceptance criteria (type: todo)
