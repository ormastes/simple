# Interpreter dispatch profiler owner missing from module tree

Date: 2026-08-21

Status: FIXED — SFFI v2 verification unblock

## Symptom

Focused `simple-compiler` tests fail before execution with Rust `E0433` at
`compiler/src/interpreter/expr.rs`: the tracked `dispatch_profile.rs` owner is
called but is not declared by `interpreter/mod.rs`.

## Impact

The defect prevents all compiler-library regression tests, including the SFFI
return-contract and dynamic-dispatch suites, from compiling. It therefore
blocks production evidence rather than representing an SFFI semantic change.

## Fix

Declare the existing level-gated module from its canonical interpreter owner.
No profiler behavior, default state, or public interface changes.
