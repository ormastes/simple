# Bug: CUDA codegen direct-device-call lowering reads a `signature` field
that `MirOperand` doesn't have

**Status:** ALREADY-FIXED — re-verified 2026-08-10. `cuda_backend.spl`'s
`compile_call` (lines ~829-873) reads the callee signature via
`self.function_signatures[name]` (a `Dict<text, MirSignature>` keyed by
function name), never via a `.signature` field on `MirOperand`. Running the
exact repro below now shows example "emits direct device calls by symbol
name" PASSING (24/28 pass; the 4 remaining failures in this file are
unrelated pre-existing defects — an `F16`/`MirTypeKind` match-exhaustiveness
bug and an argument-type-mismatch message wording difference — not this
bug).

**Date:** 2026-07-20
**Campaign:** whole-suite 01_unit triage (fix_guide.md)
**Severity:** Genuine compile-time semantic error — 1 example blocked

## Symptom

```
BIN=/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple
SIMPLE_RUST_SEED_WARNING=0 timeout 90 "$BIN" test \
  test/01_unit/compiler/codegen/cuda_backend_intensive_contract_spec.spl \
  --no-session-daemon 2>&1 | sed 's/\x1b\[[0-9;]*m//g' | grep -A2 '✗'

✗ emits direct device calls by symbol name
  semantic: class `MirOperand` has no field named `signature`
```

3 of 4 examples in the file pass (if-branch/loop-backedge PTX control flow,
global load/store + shared allocation, deprecated-atomic rejection); only
"emits direct device calls by symbol name" fails.

## Re-verification (2026-08-10)

The spec file has since grown to 28 examples. Re-ran:

```
BIN=/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple
SIMPLE_RUST_SEED_WARNING=0 timeout 90 "$BIN" test \
  test/01_unit/compiler/codegen/cuda_backend_intensive_contract_spec.spl \
  --no-session-daemon
# Results: 28 total, 24 passed, 4 failed
# "emits direct device calls by symbol name" -> PASSES
```

The `.signature`-on-`MirOperand` symptom no longer reproduces. Root cause was
already addressed upstream: `compile_call` in
`src/compiler/70.backend/backend/cuda_backend.spl` looks up the callee's
`MirSignature` from `self.function_signatures` (populated from each
`MirFunction.signature` at module-compile time, see line ~141), not from the
`MirOperand` call-target value. The 4 examples still failing in this file are
unrelated (F16 match-exhaustiveness in `MirTypeKind`, and a mismatched-arg
error-message assertion) and are out of scope for this report.

## Root-cause hypothesis (not verified against source)

The direct-device-call lowering path (invoked when compiling a CUDA kernel
that calls another device function by symbol name) appears to access a
`.signature` field on a `MirOperand` value — either a field that was
renamed/removed from `MirOperand`, or a case where the lowering should be
reading the signature off the *callee's* `MirFunction` (which does have a
`signature: MirSignature` field per `src/compiler/70.backend/backend/vhdl/
vhdl_abi_spec.spl`'s `make_simple_func`) rather than off the `MirOperand`
representing the call target.

## Reproduction

`test/01_unit/compiler/codegen/cuda_backend_intensive_contract_spec.spl`,
example "emits direct device calls by symbol name".

## Suggested follow-up

Trace the direct-device-call lowering in the CUDA backend (likely under
`src/compiler/70.backend/backend/cuda/` or similar) for the `.signature`
access on a `MirOperand`-typed value and either fix the field access or add
the missing field.
