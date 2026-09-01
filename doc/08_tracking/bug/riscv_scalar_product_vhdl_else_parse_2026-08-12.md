# Seed parser rejects the RISC-V scalar-product VHDL renderer at `else:`

Date: 2026-08-12
Status: OPEN
Severity: high — blocks the formal-verification system spec before examples run.

## Symptom

```
bin/simple test test/03_system/compiler/formal_verification_2_0_spec.spl --mode=interpreter
```

fails during compilation with:

```
error: compile failed: parse: in
".../src/compiler/70.backend/backend/riscv_scalar_product_to_vhdl.spl":
Unexpected token: expected expression, found Else
```

The runner then reports zero examples executed and a `parse-error` verdict.

## Investigation

The source was reduced from a nested expression-level `else:` branch to an
explicit statement-level LSU branch, while preserving the rejection and success
paths. The same seed-parser diagnostic remained after the focused rerun. The
diagnostic has no source location, so a further parser change would be blind.

The `bin/simple` resolved for this run is the bootstrap seed at
`bin/release/x86_64-unknown-linux-gnu/simple`, which itself warns it is not the
normal self-hosted tool.

## Unblock condition

Make the parser report the source location for this `Else` token and align the
seed and self-hosted grammars for the applicable conditional form. Then rerun
the formal-verification spec and require at least one executed example.

