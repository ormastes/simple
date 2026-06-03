# Feature: graphical_backend_equality

## Raw Request
make a plan after deepresearch $sp_dev improve test for graphical and backend equality check. make a infra for graphical and multiple backend support. and make them equvalent drawing. see next refactor to add common interface for tests.ang update tests and make them same drawings. do more local research and updte next research and plan for spawn agents and often sync with gh too >> [external graphical regression/debug layer proposal supplied in user message]

## Task Type
feature

## Refined Goal
Define the next SPipe feature lane for common graphical equality testing so shared drawing cases can run across CPU/GPU/Web/GUI/WM backends with normalized capture metadata, comparable drawings, and useful diff reports.

## Acceptance Criteria
- AC-1: Local research identifies existing repo capture, backend measurement, pixel comparison, and WM/web parity files to extend.
- AC-2: Requirement options define at least two selectable scopes and do not auto-select final requirements.
- AC-3: NFR options define explicit determinism, performance, artifact, and GitHub sync policies.
- AC-4: The plan defines a common backend/test interface for equivalent drawings across multiple backends.
- AC-5: The plan defines parallel agent workstreams with disjoint ownership and regular `jj git fetch` checkpoints.
- AC-6: The plan records that implementation must not proceed until the user selects feature and NFR options.

## Scope Exclusions
- No implementation, refactor, or SPipe spec edits in this planning pass.
- No final requirements are written until the user selects options.
- No push or rebase is performed in the existing dirty worktree.

## Phase
dev-done

## Log
- dev: Created state file with 6 acceptance criteria (type: feature).
- dev: Ran SPipe command wiring check; status PASS.
- dev: Ran `jj git fetch`; GitHub checkpoint reported `Nothing changed`.
- impl: Selected Feature Option B + NFR Option 2 from the plan and wrote final
  requirements, NFRs, architecture, design, and system test plan.
- impl: Added `wm_compare` graphical equality model, render-side capture facade,
  focused system spec, focused integration spec, and mirrored manuals.
