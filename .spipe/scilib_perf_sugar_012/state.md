# Feature: scilib-perf-sugar-012

## Raw Request
fix all remain bug and feature request and abandon plans.. and in mind pure simple is main rust is just seed. use skill $sp_dev

## Task Type
bug

## Refined Goal
Prevent scilib test runs from reporting synthetic success when no BDD example body executed.

## Acceptance Criteria
- AC-1: The test runner accepts `--assert-ran` as an explicit option.
- AC-2: `--assert-ran` fails a file result that otherwise reports success without individual BDD results, BDD runtime snapshot groups, or skip-only evidence.
- AC-3: `--assert-ran` disables the interpreter static fast path so targeted scilib specs execute instead of being counted statically.
- AC-4: Existing normal test behavior remains unchanged when `--assert-ran` is not set.
- AC-5: Regression tests cover option parsing and synthetic-success rejection.

## Scope Exclusions
This slice does not port the Rust seed runner to pure Simple and does not implement new native/SMF BDD lowering.

## Phase
dev-done

## Log
- dev: Created state file with 5 acceptance criteria (type: bug).
