# F64 call ABI guard admission contract

## Tracking and scope

This guide covers `scripts/check/check-f64-call-abi.shs`, the guard registered
by the OPEN P1 bug
`f64_self_hosted_call_result_codegen_2026-06-21`. The codegen defect and the
guard's false-success status share that row; do not create a duplicate bug.

This repair changes evidence classification only. It does not claim to repair
the self-hosted F64 call ABI or to provide Stage 4 authority.

## Exit contract

- `0`: verified self-hosted identity, correct interpreter reference, and
  correct JIT value.
- `1`: an unexpected measured semantic failure.
- `2`: untestable target or authority, including a Rust bootstrap seed. The
  existing script prints this as `SKIPPED (cannot test)` and states that it is
  not a pass.
- `3`: the measured, tracked known-bad JIT result, categorized as `XFAIL` for
  development while denied admission.

Every nonzero status is admission failure. Human-readable output must retain
`FAIL`, `SKIPPED (cannot test)`, or `XFAIL` so development diagnosis is explicit.

## Canonical owner test

The shell unit test owns this contract. It supplies isolated fake compiler
executables that emulate:

1. correct interpreter and JIT output (`0`),
2. correct interpreter plus known-bad JIT `0.0` (`3`),
3. correct interpreter plus an unexpected JIT value (`1`),
4. Rust-seed identity remains `2` when the parent sets
   `SIMPLE_BOOTSTRAP=1` or `SIMPLE_RUST_SEED_WARNING=0`; the identity probe
   clears both suppression variables,
5. a parent `SIMPLE_EXECUTION_MODE=interpret` cannot turn the JIT measurement
   into a second interpreter run; the compiled lane clears that override and
   requires strict JIT execution.

The baseline test must fail while XFAIL returns `0`; the same test must pass
after the script reserves success for the correct value. The fixture does not
stand in for a native compiler or close the underlying bug.

No direct executable caller exists in `scripts/`, `.github/`, or `test/` at
the time of this repair. `scripts/check/non_vacuity_baseline.txt` registers the
guard and the wiring scanner mentions it, but neither consumes its status as
admission. The owner unit therefore asserts the guard process boundary
directly: status `3` is nonzero and cannot be accepted by a conventional
fail-fast caller. A future direct caller needs the same boundary assertion.

`scripts/check/lib/require-self-hosted.shs` describes a three-status shared
identity contract, not this guard's property-result taxonomy. Its wording must
not be changed to imply that generic guards emit status `3`.

## Verification

Run the owner shell unit once before and once after the repair, with at most
three verify/fix cycles. Run shell syntax checks and the repository structural
gates relevant to changed script/docs. Keep the bug DB row OPEN. Obtain an
independent exact-head Astra review before push or admission.
