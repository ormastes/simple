# Bug: CUDA codegen direct-device-call lowering reads a `signature` field
that `MirOperand` doesn't have

**Status:** OPEN — filed, not fixed (source not read in depth; needs a
codegen-owner to trace `MirOperand` vs. the direct-device-call lowering
path)

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
