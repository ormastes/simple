# SFFI/non-optional fallthrough fabricates `nil`

Date: 2026-08-21

Status: CLAIMED — `/root`, SFFI v2 hardening lane

Severity: high (silent contract violation)

## Symptom

`execute_function_body` maps `Ok((_, None))` to `Value::Nil`, then applies
`validate_unit!`, which checks only declared unit types. An ordinary declared
return such as `text`, resource, or struct can therefore fall through without a
value and escape the central interpreter call path as `nil`.

## Owners

- `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`
- `src/compiler_rust/compiler/src/interpreter_call/core/macros.rs`
- pure-Simple return analysis/validation owners under `src/compiler/35.semantics/`
- parity tests under `test/01_unit/compiler/`

## Pure-Simple-first boundary rationale

The self-hosted semantic/type pipeline must reject statically provable missing
returns. The Rust interpreter still requires a runtime backstop because it
directly executes parsed functions, bodyless/extern synthesis and dynamic
control flow can reach its terminal extraction path, and the current fabricated
value is created there. The fix must not become Rust-only semantics: shared
requirements and cross-lane specs define the parity contract.

## Pre-fix reproducer

`test/03_system/compiler/fixtures/sffi_v2_missing_nonoptional_return_probe.spl` declares a `text`
function whose body produces no value and observes the call result. Record the
exact binary identity and output before and after the fix.

## Required fix

Track return origin before constructing a `Value`; allow unit fallthrough,
preserve explicit optional absence, and reject missing non-optional (plus
hardened accidental-optional) returns with stable `E-SFFI-016` semantics. Replace
the unit-only terminal check with a total return-contract validator.

## Adjacent regression coverage

- explicit unit fallthrough;
- explicit optional `nil`;
- optional plain-value auto-wrap;
- concrete `T` returning `Option.Some(T)` through an existing narrowing path;
- generator and try-error paths remain unchanged.

## Unblock condition

Exact and adjacent specs pass under the supported interpreter/run lanes, and a
deliberate reintroduction of `Value::Nil` for missing origin makes the exact
fixture red.
