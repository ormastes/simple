# Stage-4 surface release marker order failure

## Status

Open. Marker framing is fixed, but streaming builder state still loses surfaces
before an alias is resolved.

## Reproduction

Run `scripts/check/check-stage4-selfhost-module-release-slope.shs --live` around
the low-memory, entry-closure Stage-4 build of `src/app/cli/main.spl` using
`build/stage4-streaming-stage3/simple`.

Required activation:

- `SIMPLE_BOOTSTRAP_STAGE4=1`
- `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1`
- mode `aot`
- low-memory `1`
- backend `cranelift`

## Evidence

- Stage-3 compiler build: 674 compiled, 0 failed.
- Stage-3 canonical candidate frontend smoke: PASS.
- Checker activation: enabled.
- The original opaque ordering failure was two un-terminated `eprint` records
  concatenated with a runtime error. Release records now end in one newline.
- Self-hosted `Result` helper-method dispatch was replaced with exhaustive
  matching.
- `ModuleSurfaceBuilder` whole-struct return/assignment, assigned array `push`,
  and an alias bounds guard were added.
- Final diagnostic after those fixes:
  `invalid physical module surface index for alias:
  path=src/lib/nogc_async_mut/cli/log_modes.spl index=8 len=2`.
- The producer emitted nine release records before the alias failure, while the
  retained surface array contained only two entries.
- No Stage-4 binary or bounded-slope PASS was produced.

The checker self-test covers valid termination, early EOF, invalid heap, invalid
sequence, and out-of-order sequence while proving process-group cleanup.

## Next step

Add bounded state diagnostics around the unique-source helper input, post-add
builder, caller match assignment, and post-`ast_reset` builder. Preserve the
four-field release record. Use that single run to distinguish self-hosted
`Result<ModuleSurfaceBuilder, text>` transport loss from `ast_reset` invalidating
the surface array or retained AST-backed values. Do not repeat the current live
command without that instrumentation.
