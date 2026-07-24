# Stage-4 surface release marker order failure

## Status

Open. Marker framing and alias indexing are fixed. The live gate reaches marker
10, but parser allocation churn exceeds the current registry-growth ceiling.

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
- The apparent alias index `8` was the native tagged representation of stored
  integer `1`. `Dict.get` is now presence-only and typed bracket reads perform
  the required untag; an index-1 alias regression covers both maps.
- The live stream now reaches marker 10 and requests termination correctly.
- Current failure: `average_growth=38913`, above the `25000` ceiling.
- No Stage-4 binary or bounded-slope PASS was produced.

The checker self-test covers valid termination, early EOF, invalid heap, invalid
sequence, and out-of-order sequence while proving process-group cleanup.

## Next step

A gated total-allocation probe measured each phase before being removed:

- surface extraction: 73–128 registry entries per sampled physical module;
- reset/release boundary: about 60 entries;
- `parse_full_frontend`: 490–101361 entries, including 34933 for
  `log_modes.spl`, 42835 for `args_and_os_commands.spl`, 101361 for
  `main_and_help.spl`, and 57539 for `cli_helpers.spl`.

`rt_heap_registry_count` is a no-GC diagnostic registry count; rich parser
temporaries remain registered for process lifetime. The slope therefore
measures parser allocation churn, not retained ModuleSurface size. Next work
must profile and reduce repeated rich frontend materialization (starting with
the high-allocation CLI modules), or replace the gate with an approved live
retention metric. Do not delete semantic surface fields or raise the threshold:
the probe shows surface construction is not the dominant cost.
