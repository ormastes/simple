# Feature: scilib-perf-sugar-006

## Raw Request
fix all remain bug and feature request and abandon plans.. and in mind pure simple is main rust is just seed. use skill $sp_dev

Selected tracker: `doc/08_tracking/feature_request/scilib_perf_sugar.md`, `PERF-SUGAR-006`.

## Task Type
feature

## Refined Goal
Make DataFrame `Symbol` values carry stable intern ids and use those ids for column-name comparisons in DataFrame selection, grouping, joins, and transform helpers.

## Acceptance Criteria
- AC-1: The Rust seed registers `rt_intern_symbol(text) -> i64`, returning the same positive id for equal text within a process and different ids for different text.
- AC-2: `Symbol.from(text)` stores both the original text and the intern id so existing display/name construction behavior remains available.
- AC-3: DataFrame column lookup and transform duplicate/name comparisons use `Symbol` intern ids instead of whole-symbol/text equality.
- AC-4: Focused tests prove symbol interning identity, column selection, rename/duplicate handling, groupby, and transform name comparisons still behave correctly.
- AC-5: `PERF-SUGAR-006` is updated with the implemented behavior and verification evidence.

## Scope Exclusions
Global symbol interning outside DataFrame/scilib names, persistent ids across processes, and non-DataFrame string equality optimizations are out of scope.

## Phase
dev-done

## Log
- dev: Created state file with 5 acceptance criteria (type: feature).
- dev: Implemented `rt_intern_symbol(text) -> i64` in the Rust seed interpreter.
- dev: Wired sync-mut and async-mut DataFrame `Symbol` through intern ids while preserving label text.
- dev: Added `test/03_system/feature/scilib/df_symbol_intern_spec.spl` covering symbol identity, select, rename, groupby, concat, merge, melt, and pivot behavior.
