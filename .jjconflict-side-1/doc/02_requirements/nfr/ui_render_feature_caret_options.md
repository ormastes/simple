# NFR Options: UI Render Feature Caret

**Date:** 2026-04-03
**Status:** Selection required

## Option N1: Functional baseline

Targets:
- one shared command surface
- deterministic text/html output
- Docker/headless-safe execution

Pros:
- fastest path
- enough for CI and screenshots

Cons:
- weak enforcement on parser drift and app adoption

Effort:
- low

## Option N2: Production-ready shared runtime

Targets:
- startup under 250 ms warm for headless render of default sample
- deterministic output across repeated runs
- one parser authority
- config precedence documented and tested
- app adapters for GUI-like apps

Pros:
- practical default for repo-wide rollout
- enforceable without over-design

Cons:
- requires tests and migration guardrails

Effort:
- medium

## Option N3: Strict architecture enforcement

Targets:
- all N2 targets
- explicit layer ownership for render feature carets
- no app-local render flags outside shared adapters
- CI checks for parser/help/config drift
- documented layer contracts and transform boundaries

Pros:
- strongest long-term maintainability
- prevents regression into app-local special cases

Cons:
- highest initial cost
- requires more tooling and validation work

Effort:
- high

## Recommendation

Recommended starting point: **Option N2**
