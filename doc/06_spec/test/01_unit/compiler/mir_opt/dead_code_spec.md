# Dead Code Elimination Skeleton Specification

## Contract

`DeadCodeElimination` remains in requested optimization pipelines for
compatibility, but its registry status is `Skeleton`, its expectation is
`NeverTransforms`, and effective pipelines exclude it.

Every callable transformation surface returns the input `MirFunction`
unchanged. The compatibility observability API fails closed: instructions are
treated as potentially observable and intrinsic names are not proof of purity.
The probe-classification helper remains analysis-only support and does not
authorize deletion.

## Performance and memory contract

The Skeleton path must not build liveness, scan every block/local pair, create
per-block keep bitmaps, rebuild instruction arrays, or iterate to a fixed point.
Its counters remain zero.

## Activation gates

DCE may become a transform only after exhaustive MIR opcode contracts cover
definitions, uses, traps, effects, ownership and destruction, unwinding,
volatile/atomic/device operations, and debug probes. Rehabilitation also needs
sparse/worklist liveness with explicit compile-time and memory budgets,
positive and negative witnesses, semantic differential tests, and IR
verification.

Source: `test/01_unit/compiler/mir_opt/dead_code_spec.spl`
