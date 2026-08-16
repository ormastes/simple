# hwir_foundation_spec residual failures after missing std.spec import fix (2026-08-16)

## Context
The mass failure of `test/01_unit/compiler/50.mir/hwir_*` specs (batch timeout at
550s, per-spec 100% fail) had an infra root cause: commit `6fe33f889dee`
"test(hwir): modernize foundation specifications" (and sibling modernizations)
added `step("...")` calls to 7 specs WITHOUT adding `use std.spec.*`, so every
test in those files errored with `semantic: function 'step' not found`.

Fixed 2026-08-16 by inserting `use std.spec.*` in:
- hwir_foundation_spec.spl, hwir_mir_function_extract_spec.spl,
  hwir_zca_load_effect_outcomes_spec.spl, hwir_zca_rv64_contract_spec.spl,
  hwir_zca_rv64_ld_sd_rows_spec.spl, hwir_zca_rv64_rows_spec.spl,
  hwir_zca_rv64_stack_memory_rows_spec.spl

After the fix: all four zca_rv64/load_effect specs and the contract spec are
fully GREEN (2/2, 4/4, 2/2, 4/4, 4/4); hwir_foundation_spec went 0/50 -> 29/50;
hwir_mir_function_extract_spec 41/55 (14 residual substantive failures).

## Residual (owned by riscv_gen2_hwir_foundation lane)
`test/01_unit/compiler/50.mir/hwir_foundation_spec.spl`: 21 remaining failures,
all substantive against the HWIR slice, not test infra:
- 17x `expected false to equal true` (strict lowering / row-construction
  predicates returning false)
- 2x `expected subject to be truthy, got false`
- 1x `semantic: invalid assignment: complex indexed field receiver is not
  supported` (interpreter limitation hit by a test body)
- 1x diagnostic-code mismatch: got `HWIR-E-VHDL-IDENTIFIER: module name is not
  a stable VHDL identifier`, expected `HWIR-E-MODULE-SUMMARY: module summary
  requires a concrete matching profile`

These look like the spec asserting behavior the current
`src/compiler/50.mir/hwir/*` + `src/compiler/70.backend/backend/hwir_to_vhdl.spl`
slice does not yet implement (or diagnostics reordered). Left to the
`.spipe/riscv_gen2_hwir_foundation` lane, which owns these modules and specs.

## Unblock condition
riscv_gen2_hwir_foundation lane reconciles hwir_foundation_spec expectations
with the current strict HWIR lowering/diagnostic order, or implements the
missing behavior. Repro: `bin/simple test
test/01_unit/compiler/50.mir/hwir_foundation_spec.spl`.
