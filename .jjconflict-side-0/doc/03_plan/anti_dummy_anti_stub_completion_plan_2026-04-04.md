# Anti-Dummy / Anti-Stub Completion Plan

**Date:** 2026-04-04  
**Status:** In progress  
**Scope:** complete the repo's static enforcement against placeholder implementations and placeholder tests

## Goal

Promote anti-dummy / anti-stub from "real but incomplete" to:

- production placeholder bodies are detected by default
- placeholder SSpec examples are blocked by default
- sanctioned skip / allow escapes are explicit
- remaining repo debt is tracked as migration work, not hidden as feature completeness

## Completion slice

### Production code

- detect trivial stub returns
- detect explicit placeholder function bodies (`pass_todo`, `pass_do_nothing`, `pass_dn`) when a whole function body is only a placeholder
- keep intentional `_noop_` cases and explicit allow overrides as the narrow escape hatch

### Test/spec code

- block literal tautologies
- block pass helpers inside examples
- block placeholder `Ok(_)` / `Err(_)` match arms
- block empty example bodies
- block boolean-wrapper assertions such as `expect(code != 0).to_equal(true)` when they reduce real state to a fake pass boolean

### Out of scope for this slice

- mutation testing integration
- full-tree automatic migration of existing placeholder-heavy specs
- repo-wide hard fail on every current historical placeholder without allow/migration cleanup

## Agent work split

### Agent A
- production stub detection semantics
- placeholder body detection

### Agent B
- SSpec placeholder detection
- empty-body and boolean-wrapper heuristics

### Agent C
- migration audit docs and TODO tracking

### Main agent
- integration
- regression specs
- docs and status wording

## Acceptance

- new lint codes exist for explicit placeholder function bodies and stronger SSpec dummy patterns
- targeted regression specs pass
- docs distinguish implemented enforcement from remaining migration debt
