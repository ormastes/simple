# Feature: macro-intro-let-binding-nil

## Raw Request
fix all remain bug and feature request and abandon plans.. and in mind pure simple is main rust is just seed. use skill $sp_dev

Tracker: doc/08_tracking/bug/macro_intro_let_binding_nil_2026-05-30.md

## Task Type
bug

## Refined Goal
Make macro `intro result: enclosing.module.let` emissions bind usable values in the caller scope instead of evaluating to nil.

## Acceptance Criteria
- AC-1: `bin/simple run test/feature/usage/macro_validation_spec.spl` no longer reports nil results for `intro let` assertions.
- AC-2: Existing `intro fn` macro validation behavior still passes in the same spec.
- AC-3: The fix does not weaken, skip, or replace the failing macro validation assertions with placeholder passes.
- AC-4: The bug tracker records the fixed status with the verification command used.

## Scope Exclusions
Broader macro hygiene naming behavior outside the documented nil-binding failure is not part of this slice unless required to make the existing assertions pass.

## Phase
verified

## Log
- dev: Created state file with 4 acceptance criteria (type: bug).
- implement: Captured emitted macro-intro variable values and substituted template binding patterns in the Rust seed interpreter path.
- verify: `cargo check -p simple-compiler --manifest-path src/compiler_rust/Cargo.toml` passed with existing warnings.
- verify: `cargo build -p simple-driver --manifest-path src/compiler_rust/Cargo.toml` passed with existing warnings.
- verify: `SIMPLE_LIB=src src/compiler_rust/target/debug/simple run test/feature/usage/macro_validation_spec.spl` passed all macro validation groups.
- verify: `SIMPLE_LIB=src src/compiler_rust/target/debug/simple check test/feature/usage/macro_validation_spec.spl` passed.
