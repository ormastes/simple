# MIR AOP Injection Spec

Source: `test/01_unit/compiler/mir/aop_injection_spec.spl`

## Scenarios

- MIR call instructions classify as function-call join points.
- MIR store instructions classify as variable-assignment join points.
- Comparison binary operations classify as comparison join points.
- Advice call construction emits a valid MIR call instruction.
- MIR block extraction handles empty and populated block lists.

## Reproduction

```bash
bin/release/x86_64-unknown-linux-gnu/simple test test/01_unit/compiler/mir/aop_injection_spec.spl --mode=interpreter --no-cover-check
```
