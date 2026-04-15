# Anti-Dummy / Anti-Stub Completion Plan

**Date:** 2026-04-04  
**Status:** In progress

## Goal

Make anti-dummy / anti-stub enforcement a real quality feature instead of a partial lint that is easy to bypass in practice.

## Completion Target

The feature is complete when:

- production `pass_todo(...)` placeholders are denied
- spec/example tautologies are denied
- print-based skip placeholders are denied
- empty or no-assert examples are denied
- the normal lint surface reports these issues directly
- repo-wide placeholder debt is tracked explicitly for migration

## Implemented In This Pass

- `STUB003` for explicit `pass_todo(...)` in production code
- `SSPEC004` for print-based skip placeholders
- `SSPEC005` for examples with no real assertion or sanctioned skip
- pure-Simple lint path switched to use real linter results instead of fix-only reporting
- regression coverage in [sspec_quality_lint_spec.spl](test/integration/app/sspec_quality_lint_spec.spl)

## Remaining Work

- migrate legacy placeholder-heavy specs across the tree
- unify all CLI/wrapper lint entrypoints so every surface reports the same anti-dummy rules
- add a later mutation-style verification pass for high-value subsystems

## Current Debt Snapshot

A tree-wide grep still finds many legacy placeholder patterns in `src/` and `test/`.
That debt is migration work, not evidence that the new enforcement is missing.
