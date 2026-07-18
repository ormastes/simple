# Redeploy Kit 05 — nested closure reads wrong (0) for outer-captured var

## Defect (high)
A closure lexically nested inside another closure's body reads `0` for a
variable captured by the enclosing closure instead of its real value.

```
fn main():
    val base = 10
    val mul = 3
    val combo = \x:
        val step = \y: y + base   # step must read outer-of-outer `base`
        step(x) * mul
    print(combo(2))   # expected (2+10)*3 = 36, actual 0
```

## Root cause (analysis — not yet fixed)
`base` is captured by `combo`, and the INNER closure `step` must transitively
capture `base` from `combo`'s environment. The result `0` (not garbage) means
the inner closure's capture slot for `base` was allocated but never populated
with the enclosing closure's captured value — the transitive/nested capture
copies from the wrong environment (the enclosing FUNCTION frame, where `base`
is itself only a capture of `combo`, reading a zero-initialised slot).

This is the same closure-capture machinery as item 02
(`compile_closure_create` in
`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`): captures
are written from `get_vreg_or_default(ctx, ..., &captures[i])`. For a nested
closure, the capture source must be the ENCLOSING CLOSURE's capture slot (loaded
from the closure environment pointer), not a fresh/zero vreg. When the enclosing
value is itself a capture, `get_vreg_or_default` returns the default (0) because
the vreg isn't materialised in the inner closure's frame.

Fix direction (requires seed rebuild to verify): when lowering a nested closure,
resolve each transitive upvalue to a LOAD from the enclosing closure's
environment (chained capture), so `step`'s `base` slot is initialised from
`combo`'s `base` capture rather than a zero default. Align HIR/MIR capture
resolution to mark transitive upvalues and emit the environment-chain load in
codegen.

## Test plan
- Expected-behavior spec:
  `test/cert/redeploy_pending/nested_closure_capture.spl` (expects `36`).

## Verify-now vs redeploy-pending
- REDEPLOY-PENDING + NOT-YET-FIXED: root cause localized to transitive nested
  -closure capture in the frozen seed codegen; fix not implemented/verified this
  session.
