# Feature: llm-caret-claude-cli-full-parity

## Raw Request
make detail plan for every feature, file and class and function base impl plan. make very detail plan when it done nothing can skip from it.

## Task Type
feature

## Refined Goal
Create an exhaustive implementation plan for full Claude CLI parity in `src/app/llm_caret`, covering every Claude source feature, file, class, function, and type with no skipped rows.

## Acceptance Criteria
- AC-1: Every file under `tmp/claude/claude-code-main/src` has a row in the full-parity file matrix with a Simple target file, target minimum LOC, implementation action, test path, and done gate.
- AC-2: Every extracted Claude function/class/type/interface/const-function symbol has a row in the symbol matrix with a Simple target symbol and parity test gate.
- AC-3: Every generated feature group has a row in the feature matrix with source counts, target capsule, phase, and completion gate.
- AC-4: The human-readable plan explains how the matrices are consumed during implementation and defines a no-skip completion rule.
- AC-5: A checker verifies matrix row counts against the current Claude source tree and fails on missing targets, missing actions, missing gates, below-source target minimum LOC, or explicit skip/defer markers.

## Scope Exclusions
None for planning. Implementation may happen in phased commits, but the completion rule remains no skipped source files or symbols.

## Cooperative Review
Sidecar lanes recommended for implementation: commands/tools, terminal UI, bridge/remote, services/plugins/skills, support utilities. Merge owner: Codex. Final reviewer: highest-capability reviewer. Shared helper names: `full_parity_file_row`, `full_parity_symbol_row`, `expect_full_parity_gate`. Fail-fast placeholder: every planned test starts with `fail("full parity row not implemented")` until the row is implemented.

## Phase
design-done

## Log
- design: Created exhaustive full-parity plan and generated file/feature/symbol matrices from the current Claude source tree.
