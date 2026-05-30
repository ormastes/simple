# Feature: fr-compiler-012-expect-precedence

## Raw Request
Task: resolve compiler tracker item `FR-COMPILER-012` if feasible. Own only compiler-related source/tests/docs for this item, the assigned tracker entry, and `.spipe/<slug>/state.md`. Locate the exact request, define acceptance criteria, implement/close with focused tests, and final with status, changed paths, tests run, and blockers.

## Task Type
bug

## Refined Goal
Fix the parser so `expect (expr) == value` parses as one expectation over the full comparison expression.

## Acceptance Criteria
- AC-1: `expect (true and true) == true` parses and executes equivalently to `expect((true and true) == true)`.
- AC-2: A focused parser or feature test covers the precedence case without relying on placeholder assertions.
- AC-3: Existing passing `expect` syntax tests still pass.
- AC-4: The parser tracker entry for `FR-COMPILER-012` is updated to `Implemented` with verification evidence.

## Scope Exclusions
- The duplicate `FR-COMPILER-012` JIT rendering request is out of scope for this focused parser fix.
- No non-compiler source, unrelated tracker entries, or unrelated generated docs are changed.

## Phase
ship-done

## Log
- dev: Created state file with 4 acceptance criteria (type: bug)
- implement: Normalized bare `expect` comparison ASTs so `expect (expr) == value` stores the comparison inside the `expect` argument.
- spec: Added focused Rust parser coverage and replaced workaround parentheses in logical usage-spec cases.
- verify: PASS `cargo test --manifest-path /tmp/simple-final-sync/src/compiler_rust/parser/Cargo.toml --test statements -- parse_bare_expect_parenthesized_comparison_as_single_argument --nocapture`.
- verify: PASS `SIMPLE_LIB=/tmp/simple-final-sync/src /tmp/simple-final-sync/src/compiler_rust/target/debug/simple test test/feature/usage/parser_keywords_spec.spl --mode=interpreter --clean --fail-fast`.
- verify: WARN `parser_operators_spec.spl` logical cases pass under debug run, but the full file still reports unrelated assignment-operator failures.
- follow-up: Fixed the unrelated BDD augmented-assignment execution path that
  caused the full `parser_operators_spec.spl` failure.
- verify: PASS `SIMPLE_LIB=/tmp/simple-next-main/src /tmp/simple-next-main/src/compiler_rust/target/release/simple test test/feature/usage/parser_operators_spec.spl --mode=interpreter --clean --fail-fast`
  (`48/48`).
- verify: PASS `SIMPLE_LIB=/tmp/simple-next-main/src /tmp/simple-next-main/src/compiler_rust/target/release/simple test test/feature/usage/parser_keywords_spec.spl --mode=interpreter --clean --fail-fast`
  (`22/22`).
