# Stage 4 direct range and slice values fail open

- Status: fixed in the LLVM 23.1 Phase 4 integration lane
- Severity: P1 bootstrap/native correctness
- Owner: pure-Simple MIR expression dispatch

## Reproduction

`for i in range(start, end)` is lowered directly by the counted-loop owner and
is valid. A standalone range value, or `array[start:end]`, instead reached the
generic expression path. That path used an unresolved const-zero function
operand or reported a non-fatal error and returned const zero, allowing invalid
native IR or a null-derived runtime access.

## Fix

Unsupported standalone range and slice values now report fatal MIR errors and
emit a placeholder only to keep the rejected MIR structurally defined. The
fatal-error gate prevents code generation. Counted range loops remain on their
existing direct lowering path.

## Regression

`test/01_unit/compiler/mir/bootstrap_real_body_guard_source_spec.spl` asserts
both fatal diagnostics and rejects generic `self.lower_range` dispatch.
`test/fixtures/compiler/stage4_range_hir_owner.spl` executes two independent
counted loops and distinguishes the supported path.
