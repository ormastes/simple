# unit_value_binop silently truncated integer unit division (1/2 -> 0)

- Date: 2026-11-17
- Plan rows: RB-UNIT-01/02 (robust boundaries plan 2.4)
- Status: verification-pending
- Repro: `test/01_unit/compiler/units/unit_dimension_parity_spec.spl`, case
  "integer operands do not truncate 1/2 to 0" (failed on base too).

Root cause: in non-strict mode `unit_op_product_verdict` allows `U / U` to the
underlying scalar (with a SPL-UNIT-004 warning), and `unit_value_checked` then
computed `l / r` with integer division, so `Widgets(1) / Widgets(2)` became
`0`. `U / int` hit the same path.

Fix: `unit_value_binop` (src/compiler/30.types/units/unit_ops.spl) now returns
`Error(SPL-UNIT-002 ... inexact on integer payloads)` when a unit division has a
nonzero remainder; exact divisions still yield a value. The interpreter
(`src/app/interpreter/expr/arithmetic.spl`) evaluates through this shared
function. Known gap: compiled code only checks the verdict, which happens
before values exist, so the runtime remainder check is interpreter-only.
Unit values in native code still need a lowering-side check.

Prevention specs (same file): exact `4/2` yields 2, `Widgets / int` 7/2 is
an error, unit `%` is denied, `Widgets * int` stays exact.
