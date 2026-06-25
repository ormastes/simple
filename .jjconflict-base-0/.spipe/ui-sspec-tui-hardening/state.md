# Feature: ui-sspec-tui-hardening

## Raw Request
`$sp_dev  it should be update spipe skill and guide to do it. check all feature and fix any bugs in tui. tui also should support test runner debug mode with sgtti test interface. improve tui test infra through sspec whole feature system test.`

## Task Type
feature

## Refined Goal
Harden the SPipe UI testing lane so TUI/GUI-facing app features have executable SSPEC coverage, generated manuals, visible evidence metadata, and a test-runner debug TUI path that is queryable through SGTTI without adding production overhead.

## Acceptance Criteria
- AC-1: SPipe skills and guides document that UI-facing specs must use executable SSPEC scenarios, generated manuals, and visible-state evidence.
- AC-2: Test-runner session-debug mode exposes a TUI model that can be captured and queried through SGTTI.
- AC-3: Normal production test-runner entrypoints do not import SGTTI or debug-TUI capture code, and entry-closure builds can elide SGTTI.
- AC-4: UI-facing app feature specs have mirrored `doc/06_spec/...` manuals at the current `test/`-mirrored path.
- AC-5: An executable system audit verifies the critical UI evidence surfaces and generated manuals remain present.
- AC-6: Focused checks, generated-spec layout guard, and SPipe dev command wiring pass before handoff.

## Scope Exclusions
Full live GUI pixel baselines for host-dependent QEMU/browser surfaces are not required in this slice when existing specs already provide non-raster UI access, Draw IR, SGTTI, or generated manual evidence.

## Phase
dev-done

## Log
- dev: Created state file with 6 acceptance criteria (type: feature).
