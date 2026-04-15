# Anti-Dummy / Anti-Stub Multi-Agent Completion Plan

**Date:** 2026-04-04  
**Status:** Ready for concurrent implementation  
**Execution model:** parallel agents with bounded ownership  
**Goal:** make anti-dummy / anti-stub prevention a real repo-quality feature instead of only a local lint

## Completion Target

The feature is complete when the repo can truthfully say:

- changed-scope verification fails on placeholder tests and obvious stub implementations
- a full-project audit can measure the remaining legacy backlog
- local suppressions are visible debt, not a silent escape hatch
- public docs no longer imply that green tests alone mean meaningful proof

This does **not** require the entire historical test tree to be clean in one change.

It **does** require:

- a real verify/audit surface
- regression tests for the gate itself
- an explicit cleanup backlog
- a plan for later mutation-style hardening

## Current State

Already implemented:

- `STUB001` deny-by-default lint
- `SSPEC001`–`SSPEC003` deny-by-default placeholder-test lints
- regression tests for those lints

Still missing:

- repo-scoped verify/audit reporting
- visibility for local lint suppression
- tracked cleanup backlog
- consistent command path integration
- mutation-style hardening for high-value suites

## Agent Workstreams

### Agent A: Lint and Gate Semantics

**Owns**
- lint rules
- suppression policy
- regression fixtures

**Tasks**
- keep AST-first enforcement authoritative
- make local suppression visible in verify/audit output
- ensure changed-scope failures are deterministic

### Agent B: Verify Surface and Reporting

**Owns**
- verify report integration
- report artifact writing
- changed-scope vs full-project scope handling

**Tasks**
- build quality reports for selected files and `--all`
- separate test-placeholder findings from stub findings
- make report output actionable by file and line

### Agent C: Backlog and Cleanup Tracking

**Owns**
- offender inventory
- TODO/backlog integration
- migration prioritization

**Tasks**
- count remaining offenders
- identify top directories/suites
- keep a dedicated cleanup backlog doc

### Agent D: Command Surface Integration

**Owns**
- `simple verify` / `simple lint` integration path
- wrapper/runtime parity

**Tasks**
- make the quality gate reachable from a stable user-facing command
- avoid regressing existing verify flows
- document any remaining wrapper/runtime blockers explicitly

### Agent E: Future Mutation Hardening

**Owns**
- mutation-testing follow-on design
- changed-test quality measurement direction

**Tasks**
- define a bounded mutation-style pilot for high-value suites
- do not block the current lint/audit milestone on full mutation infrastructure

## Definition Of Done

The current milestone is done when:

- repo-scoped audit exists
- changed-scope audit exists
- suppressions are surfaced
- backlog is documented
- lint and gate regression tests pass

The follow-on milestone is mutation-style hardening.
