# Seed unary negation loses narrow signed width

- Status: fixed in this change; bootstrap generation rebuild remains separate.
- Scope: Rust bootstrap seed interpreter and Cranelift JIT.
- Base: release/1.0.0 at a45bce4460af98f6c1fe787febe426f2eac1086b.
- Related: `seed_i32_overflow_interp_vs_jit_divergence_2026-11-05.md`.

## Requirement and reproduction

REQ-SEED-SIGNED-NEG: unary minus preserves the declared i8/i16/i32 width,
including direct expression use, parameters, casts and inferred bindings.
Negating the signed minimum wraps back to that minimum, consistent with the
existing signed arithmetic contract. Ordinary negatives, zero, i64, floats and
unsigned interpreter operations retain their existing behavior.

The installed bootstrap seed printed `128 32768 2147483648` when negating
variables declared i8=-128, i16=-32768, i32=-2147483648 in both interpreter and
JIT modes. This was reproduced again by Rust integration tests built against
the release source above: four narrow-width tests failed and the independent
wide/float/unsigned interpreter control passed.

`test/fixtures/seed_interp/signed_unary_negation_repro.spl` is a standalone
bootstrap diagnostic with five real assertions. Automated evidence below
comes from the Rust integration tests, which parse and execute Simple source
through the actual interpreter and JIT APIs, not from a deployed CLI.

## Causes and repair

1. Interpreter integer negation operated on widthless `Value::Int(i64)`.
   Reuse existing `static_int_width` and `wrap_signed` at the unary boundary.
2. JIT negation operated on widened i64 storage and narrow return values could
   be zero-extended by generic ABI handling. Narrow signed results now wrap
   and are sign-extended to i64 before leaving the unary instruction owner.
3. The MIR inliner replaced a typed parameter load with a copy of its caller
   argument. A concrete post-inline trace had `Store ty=i32`, then `Copy` of
   an i64 argument, followed by unary negation. Keep the existing typed slot
   load for i8/i16/i32, following the existing float-parameter rule.

No public API or runtime ABI changes. The inliner retains its existing store
and load instead of forwarding a value whose declared type differs.

## Verification

`compiler/tests/seed_signed_unary_negation.rs` has six integration tests:

- Three interpreter tests PASS: minima and double negation at all three widths;
  parameters/casts/inferred bindings; i64/f64/u8 controls.
- Three JIT tests PASS: minima/double negation; inlined parameters/casts and
  wide controls; direct non-inlined function calls with minima, +7, -7 and
  zero at all three widths.
- Existing `i32_overflow_wrap_jit`: 2 PASS.
- Existing `inline_float_param_jit`: 2 PASS.

Commands used an isolated Cargo target and
`CARGO_PROFILE_TEST_DEBUG=0 CARGO_PROFILE_TEST_OPT_LEVEL=0`, package
`simple-compiler`, test targets above, four build jobs. Baseline: 1 PASS,
4 FAIL. Final interpreter evidence was retained while repairing the JIT;
final JIT-only run: 3 PASS, 3 filtered out. Adjacent regressions: 4 PASS.

Local logs: `/tmp/seed-signed-negation-before-build.log`,
`/tmp/seed-signed-negation-after-build.log`,
`/tmp/seed-signed-negation-jit-final.log`, and
`/tmp/seed-signed-negation-adjacent-tests.log`.

Direct-env working/staged guards PASS; executable-spec layout count is zero.
This evidence qualifies the focused seed repair. It does not qualify a rebuilt
seed-to-Phase-3 chain or replace self-hosted CLI/MCP admission evidence.
