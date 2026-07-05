# Feature: llm-caret-claude-cli-harden

## Raw Request
$sp_dev Llm caret harden, with claude cli code. extract features. make sspec system tests. and match each source files to llm caret source code files and check least file loc reach 80% or more. And check all function and class tracing tables. llm caret should follow mdsoc+ while migrate claude cli feature. may update namings and others to meet simple conventions. check files on tmp/claude/ which is claude source codes.

## Task Type
feature

## Refined Goal
Harden the LLM caret Claude CLI lane by tracing Claude-source features into the Simple `src/app/llm_caret` caret, proving at least 80% source-file mapping coverage, and adding an executable SSpec gate for the trace contract.

## Acceptance Criteria
- AC-1: `doc/09_report/llm_caret_claude_cli_traceability.md` lists extracted Claude CLI feature groups from `tmp/claude/claude-code-main/src` and maps each `src/app/llm_caret/*.spl` source file to Claude source files or an explicit Simple-only role.
- AC-2: The trace report includes function/class tracing tables for every `src/app/llm_caret/*.spl` file and key Claude CLI source files used for migration.
- AC-3: A checker computes current `src/app/llm_caret/*.spl` file and LOC mapping coverage and fails if either drops below 80%.
- AC-4: The checker verifies every current `fn`, `struct`, and `extern fn` symbol in `src/app/llm_caret/*.spl` appears in the Simple symbol trace table.
- AC-5: An executable SSpec system test runs the checker and validates the trace report exists, contains MDSOC+ ownership notes, and reports `STATUS: PASS`.
- AC-6: Existing unrelated dirty files are preserved and not folded into this lane.

## Scope Exclusions
Live Claude API calls, OAuth/remote-control parity, TUI React/Ink parity, process supervision, and broad JSON-helper deduplication are out of scope until a follow-up requirement selects them.

## Cooperative Review
N/A: this turn is a focused traceability and gate lane. Merge owner: Codex. Final reviewer: highest-capability reviewer before release. Shared helper: `check-llm-caret-claude-cli-trace.shs`. Manual flow step: `step("Run the traceability checker")`. Fail-fast placeholder: checker exits nonzero on missing trace rows or coverage below 80%.

## Phase
dev-done

## Log
- dev: Created state file with 6 acceptance criteria (type: feature).
- dev: Tightened checker to enforce LOC-weighted coverage and complete Simple symbol trace coverage.
