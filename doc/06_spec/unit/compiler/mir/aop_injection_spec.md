# MIR AOP Injection Spec

Source: `test/01_unit/compiler/mir/aop_injection_spec.spl`

## Scenarios

- MIR call instructions classify as function-call join points.
- MIR store instructions classify as variable-assignment join points.
- Comparison binary operations classify as comparison join points.
- Advice call construction emits a valid MIR call instruction.
- MIR block extraction handles empty and populated block lists.
- Prepared execution advice creates one stable slot and one automatic MIR
  dispatch per admitted before/success/error phase, even when multiple rules
  share a phase.
- Prepared `around` advice fails closed because no exactly-once proceed
  continuation exists.
- Prepared entry placement follows `MirFunction.entry_block` even when blocks
  are reordered, and canonical signature/symbol identity distinguishes overloads.

## Reproduction

```bash
bin/release/x86_64-unknown-linux-gnu/simple test test/01_unit/compiler/mir/aop_injection_spec.spl --mode=interpreter --no-cover-check
```
