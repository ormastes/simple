# Feature: P2/P3 Bug Sweep

## Raw Request
$sp_dev fix all p2 p3 bugs. fix not verify makie reproduce tests and simliar bug tests add and push them.

## Task Type
bug

## Refined Goal
Fix every currently open, host-fixable P2 and P3 BugDB defect at the owning boundary, add an exact pre-fix reproducer and an adjacent root-cause regression for each fix, update authoritative knowledge, and push the source-and-test changes without converting unavailable external evidence into completion.

## Acceptance Criteria
- AC-1: Snapshot the current canonical BugDB inventory and enumerate every open P2/P3 record with its priority, status, owner, reproduction command, and host/capability requirement; resolved, duplicate, and evidence-only rows must be justified individually rather than silently excluded.
- AC-2: Claim each actionable bug record before editing and retain the exact failing reproduction once; the record names the observed failure, first faulty boundary, intended owner, and acceptance command.
- AC-3: Fix the pure-Simple owner first for each defect. Rust/runtime edits are permitted only when retained evidence proves correct pure-Simple delegation and identifies the lower boundary; that proof is recorded in the bug file.
- AC-4: Every implemented fix has one exact regression and at least one adjacent/similar root-cause detector. Each acceptance criterion is executed at most once after convergence, with no more than three verify/fix cycles per bug.
- AC-5: P2/P3 records requiring unavailable hardware, another host, an admitted compiler, or an owner policy decision remain open with a canonical Todo DB row, exact resume command, required retained artifacts, owner, and final reviewer; postponement is not counted as a fix.
- AC-6: No unrelated dirty work is staged or committed. Each bounded batch passes scoped diff checks, direct-environment guards when applicable, numbered-artifact guards, and the focused exact/adjacent tests before push.
- AC-7: Knowledge is refreshed in the same change: affected `doc/08_tracking/bug/` records and Todo DB rows are updated; relevant `doc/` plans and `doc/07_guide/` pages are updated or marked N/A with reason; matching `doc/00_llm_process/feature_expert/<feature>/skill.md` and `doc/00_llm_process/layer_expert/<layer>/skill.md` entries are updated or created. Workflow/SSpec surfaces under `doc/06_spec`, `.codex/skills`, `.agents/skills`, `.claude/skills`, `.claude/agents/spipe`, `.claude/commands`, and `.gemini/commands` are N/A unless a fix changes those contracts.
- AC-8: Before each push, the current remote is fetched, the bounded commit is rebased onto current `origin/main`, and the pushed revision is confirmed equal to `origin/main`.

## Scope Exclusions
- P0/P1 bugs are outside this sweep.
- Closed bugs are not reopened without contradictory current evidence.
- External hardware/runtime qualification is not fabricated and does not become a source workaround.
- This implementation sweep does not claim release or umbrella verification completion.

## Cooperative Review
- Inventory sidecar: lower-cost agent classifies P2/P3 BugDB rows and proposed exclusions.
- Fix sidecars: independent agents own disjoint bug records only after shared names and acceptance commands are fixed.
- Merge owner: root Codex.
- Final reviewer: normal/highest-capability Codex reviews every broad exclusion and done mark.
- Shared interface names: `P2P3BugInventoryEntry`, `p2_p3_bug_reproduction`, `p2_p3_adjacent_regression` (planning names; production owners retain domain-specific APIs).
- Manual flow helpers: N/A unless a scenario-oriented SSpec is required; then use `step("Reproduce the exact failure")`, `step("Exercise the repaired owner")`, and `step("Reject the adjacent regression")`.
- Setup/checker helpers: existing domain-specific checkers; any new checker is named `check-<bug-slug>.shs` and fails closed.
- Fail-fast placeholders: `assert(false)` or `fail(...)` only during scaffolding and removed before commit.
- Generated-manual review owner: root Codex when any scenario manual changes; otherwise N/A.

## Phase
dev-done

## Log
- dev: Created state file with 8 acceptance criteria (type: bug).
