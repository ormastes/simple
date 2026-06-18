# Feature: browser-html-layout-renderer-count-pass-allocation

## Raw Request

`$sp_dev doc/03_plan/agent_tasks/browser_html_layout_renderer_count_pass_allocation.md`

## Task Type

bug

## Refined Goal

Prove the browser HTML layout renderer's preallocation count pass remains aligned with parser node materialization for decoded entity-only whitespace around tags.

## Acceptance Criteria

- AC-1: The resume plan exists at `doc/03_plan/agent_tasks/browser_html_layout_renderer_count_pass_allocation.md` and records the prior landed count-pass allocation fix.
- AC-2: A focused unit test covers HTML containing `&nbsp;` entity-only whitespace around tags and asserts parser allocation/materialization behavior without placeholder passes.
- AC-3: The focused count-pass unit spec passes with one lane-scoped verification command.
- AC-4: Unrelated dirty or conflicted worktree files remain outside this lane's edits.

## Scope Exclusions

- No broad renderer parity sweep.
- No broad SPipe doc generation.
- No unrelated conflict resolution or worktree cleanup.
- No release or version bump.

## Phase

verified

## Log

- dev: Created state file with 4 acceptance criteria (type: bug).
- implement: Added a focused `&nbsp;` tail-whitespace count-pass regression spec and debug hooks for allocated and materialized HTML layout parser node counts.
- verify: `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl` passed.
- verify: `bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl` did not return before the 120s tool timeout; no pass/fail result was produced.
- verify: Split the regression into `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_count_pass_spec.spl`.
- verify: `bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_count_pass_spec.spl` passed.
- spec-doc: Generated `doc/06_spec/test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_count_pass_spec.md` with `bin/simple spipe-docgen test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_count_pass_spec.spl --output doc/06_spec`.
- verify: `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.
