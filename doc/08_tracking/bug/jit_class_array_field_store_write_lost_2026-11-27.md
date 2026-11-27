# JIT loses a class-array field store across a method call boundary
## Registered 2026-11-27 by p3sweep2 lane (residual of engine_specs_spec_runner_interpreter_divergence_2026-09-16)

**Status:** OPEN
**Severity:** P3
**Lane observed:** Windows x86_64, fresh HEAD seed (build-commit d40623d3f59)

## Symptom

Under the JIT lane, a positioned node produces different pixels than the
interpreter lane in `renderer3d_bugfix` shapes: `NodeStore3D.set_position`'s
`self.nodes[i] = updated` write is lost on the JIT path — the second render
sees the pre-move position. Plain class-array stores in single-function probes
pass on both engines, so the trigger involves the method-call/array-field
combination, not array stores generally.

Minimal repro and full evidence:
`build/p3cache/engspec/render_probe.spl` (draw_calls=1 under JIT; second
render uses the stale position) plus `place_probe.spl`/`place_probe2.spl`
controls. Collected in `build/p3cache/engspec/EVIDENCE.md` (section R2) by the
p3sweep2 wave-6 lane.

## Classification

Not part of `engine_specs_spec_runner_interpreter_divergence_2026-09-16`
shapes 1-4 (those are closed at tip or fixed by that lane). This is a deeper
JIT mutation-visibility defect: a write through a class field whose value is
an array, performed inside an impl method, is not observed by a later read on
the JIT path. Interpreter lane is correct.

## Suggested starting points

- JIT place/field lowering for class-typed array fields across call
  boundaries (src/compiler_rust JIT lanes; the pure-Simple 50.mir lowering
  should be checked for the same shape via an in-process MIR probe).
- Compare with the interpreter's alias/copy semantics for the same shape
  (doc/04_architecture/compiler/array_value_abi_contract.md).

## Acceptance

A repro where `store.set_position(i, pos)` followed by a read of
`store.nodes[i].position` returns the new position on BOTH the JIT and
interpreter lanes, pinned by a regression spec under
test/01_unit/compiler (mir or jit family).
