# Seed interpreter regression: qualified `Span.empty()` dispatches to `empty(shape)`

**Status:** candidate root fix in source; executable regression and focused
runner rebuild remain pending.

## Symptom

A freshly-built seed can fail during the first HIR declaration with:

```
error: semantic: function expects argument for parameter 'shape', but none was provided
```

The focused font runner reached this after parsing its six-module closure and
entering HIR declaration for `sffi/cli.spl`.

## Root cause

The diagnostic is real argument binding against the wrong function. The first
executable HIR-declaration call is `Span.empty()`. Multiple bare-name `Span`
types overwrite the interpreter's flat class registry. For an uppercase
receiver the parser uses the `Path` call route; when the surviving `Span` lacks
`empty`, that route used to fall through to the unrelated global tensor factory
`empty(shape)`. The binder then correctly reported its missing `shape` argument.

## Impact (critical for the redeploy)

The defect blocks strict native-builds before MIR/object emission, including the
focused font evidence runner needed to calibrate pure-Simple SSpec execution.

## Fix

For known type receivers, the Rust interpreter now consults preserved
`CLASS_OVERLOADS` definitions when the flat class lacks the requested static
method, and it no longer degrades that qualified call to a bare global function.
The regression source combines two `CollisionSpan` definitions with an unrelated
`empty(shape)` and requires `CollisionSpan.empty()` to return its static marker.

## Verification handle

`cargo check -p simple-compiler` passes. Rust test binaries are currently blocked
before execution by unrelated undefined `spl_arg_count`/`spl_get_arg` symbols.
After that linker defect is cleared, run the focused runner build once and
require HIR declaration to pass without the `shape` diagnostic; no PASS is
claimed until the resulting runner is calibrated against deliberate-fail and
zero-example fixtures.
