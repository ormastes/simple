# Seed interpreter regression: qualified `Span.empty()` dispatches to `empty(shape)`

**Status:** unresolved blocker. The first candidate fix is disproven by three
bounded rebuild traces; no focused runner executable exists.

## Symptom

A freshly-built seed can fail during the first HIR declaration with:

```
error: semantic: function expects argument for parameter 'shape', but none was provided
```

The focused font runner reached this after parsing its six-module closure and
entering HIR declaration for `sffi/cli.spl`.

## Confirmed diagnosis

The diagnostic is real argument binding against the wrong function. The first
executable HIR-declaration call is `Span.empty()`. Multiple bare-name `Span`
types exist, and the unrelated tensor factory
`src/lib/nogc_sync_mut/src/tensor/factory.spl::empty(shape)` is also present in
the closure. With `SIMPLE_INTERPRETER_CALL_TRACE=empty`, every attempted focused
runner rebuild ends with an unmatched `[interp-call] enter empty` immediately
before the missing-`shape` diagnostic. The exact qualified-dispatch branch and
lost owner identity still need a targeted trace; the existing call trace emits
only the selected bare function name.

## Impact (critical for the redeploy)

The defect blocks strict native-builds before MIR/object emission, including the
focused font evidence runner needed to calibrate pure-Simple SSpec execution.

## Disproven fixes

The pushed `Path` candidate consults `CLASS_OVERLOADS` and suppresses a bare
fallback only when the receiver is already recognized as a type. It passes its
small `CollisionSpan.empty()` probe but does not fix the real closure. Three
additional experiments were applied, rebuilt, traced, and then reverted because
the real failure remained unchanged:

1. Move the `FieldAccess` bare-function fallback after static recovery.
2. Remove the early `Path` bare-function fallback.
3. Preserve `Type__method` exports for selected group imports.

Retained logs:

- `build/font-runner-fieldaccess-fixed/native-build.log`
- `build/font-runner-path-fallback-removed/native-build.log`
- `build/font-runner-group-static-import/native-build.log`

Each ends with bare `empty`, exit 1, and no runner artifact. Do not repeat these
three experiments without new dispatch-owner evidence.

## Separate deployed-runtime blocker

The available pure-Simple release ELF
`release/x86_64-unknown-linux-gnu/simple` (SHA-256
`04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`)
links an obsolete two-argument `rt_env_set`. GDB proves current callers pass
`key_ptr,key_len,value_ptr,value_len`, but that artifact's `rt_env_set`
disassembly consumes only the first two registers and passes `key_len` as the
`setenv` value pointer. `test --help` and the source font runner therefore exit
139. Current runtime sources already implement the four-argument ABI; rebuild
and relink after the seed dispatch blocker is fixed rather than adding a CLI or
font workaround.

## Verification handle

`cargo check -p simple-compiler` passes. Rust test binaries remain blocked before
execution by unrelated undefined `spl_arg_count`/`spl_get_arg` symbols. Before
another seed rebuild, extend the narrow interpreter trace to record the callee
AST route, qualified receiver, selected function owner, and signature only when
the selected name is `empty`. Then make one owner-preserving fix and require the
focused runner build to pass HIR/MIR/link. A PASS still requires the resulting
runner SHA-256 plus deliberate-fail and zero-example calibration logs.
