# SFFI/non-optional fallthrough fabricates `nil`

Date: 2026-08-21

Status: RESOLVED 2026-08-21 — the total return-contract validator existed but had
ZERO call sites; it is now wired into the terminal extraction path. Evidence below.

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


## Root cause, precisely (2026-08-21)

`validate_sffi_return_contract` and `SffiReturnOrigin` were already implemented
and unit-tested in
`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs` — and
were **dead code**: `grep -rn 'validate_sffi_return_contract|SffiReturnOrigin'`
over the whole seed returned hits in that one file only, none of them a call
from the execution path. `execute_function_body` still did

```rust
Ok((_, None)) => Value::Nil,          // origin erased here
...
validate_unit!(&result, func.return_type.as_ref(), ...)   // unit types only
```

so a declared `text`/struct/resource return with no produced value was laundered
into `nil` exactly as filed, and `validate_unit!` — which only inspects declared
UNIT types — waved it through.

## Fix

Same file. The terminal extraction now carries the ORIGIN alongside the value
(`ExplicitReturn` / `ExplicitOptionalNone` / `TailValue` / `UnitFallthrough` /
`MissingReturn` / `ForeignRawResult`, the last for the `TryError` arm), a body
that produced no value is classified `UnitFallthrough` only when the declared
contract is Unit and `MissingReturn` otherwise, and the unit-only
`validate_unit!` call is replaced by `validate_sffi_return_contract`, which is
total over the contract. Auto-wrap of `T?` returns and the symmetric
`Some(x) -> x` narrowing are untouched and still run before validation.

## Evidence

Fixtures under `test/03_system/compiler/fixtures/`, `SIMPLE_EXECUTION_MODE=interpret`:

| probe | old seed (`bin/simple`, 59,947,080 B) | new build (59,971,528 B, 14:53) |
|---|---|---|
| `sffi_v2_missing_nonoptional_return_probe.spl` | `nil` | `error: semantic: missing return in non-unit function 'missing_text'` (E-SFFI-016) |
| `sffi_v2_explicit_optional_nil_probe.spl` | `NONE_OK` | `NONE_OK` |
| `sffi_v2_unit_fallthrough_probe.spl` | `UNIT_OK` | `UNIT_OK` |

The pre-existing cargo unit tests in the same file
(`sffi_return_contract_rejects_missing_non_optional_return`,
`..._preserves_unit_fallthrough`, `..._preserves_explicit_unit_fallthrough`,
`..._preserves_explicit_optional_nil`, `..._preserves_explicit_generic_option_nil`,
`..._rejects_explicit_nil_for_non_optional_return`) stop being dead coverage and
now guard a live path; reverting the wiring makes the exact fixture print `nil`
again.
