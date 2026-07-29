# WM Native Regression Gate Blockers — 2026-07-29

## Self-hosted source closure

The WM system and GUI shortcut specs initially stopped because the
repository-wide source closure reached:

```text
src/lib/skia/feature/shaper/ot_layout_shaper.spl
Unexpected Dedent
```

The conditional at that location and the unparenthesized multiline GPOS
variation-store condition have now been normalized to the older Phase-3
grammar. The focused `ot_layout_gpos_data.spl` source-entry closure builds and
links successfully with the existing Phase-3 compiler. The capped full WM
closure has not been retried, and no bootstrap was run.

## Freestanding aggregate regression

The targeted native parity fixture
`trait_optional_struct_return` now covers concrete-to-trait dispatch,
aggregate-by-value, module-global aggregates, aggregate `Option`/`Result`,
arrays in returned structs, and nested aggregate returns.

Its LLVM native build fails with:

```text
semantic: variable fld_base_sym not found
```

The second backend made no progress and was stopped once. Per the repository
runaway guard, neither command is retried in this session.

## Host runtime availability

The host initially had no system `libglfw.so`. A retained local GLFW runtime
under `build/wm_harden/glfw_root` later enabled the focused Xvfb probe, which
proved non-black presentation plus native key, text, pointer, clipboard, and
generation-safe teardown. That boundary is green; it is not full WM scene
evidence.

## Full hosted native entry

The checked hosted entry
`examples/06_io/ui/wm_full_stack_demo.spl` passes the one-file semantic check.
Its first entry-closure native build emitted no progress or diagnostic for
roughly 2.5 minutes:

```text
bin/simple native-build --entry examples/06_io/ui/wm_full_stack_demo.spl \
  --entry-closure -o /tmp/simple_wm_full_stack_demo
```

It was terminated once with exit 143. The command is not retried in this
session; the native build therefore remains unproven rather than inferred
from the semantic check.

## Pure-Simple Phase 3 entry build

At user direction, the seed-driven build was stopped and the existing
aggregate-fix Phase 3 compiler was used directly:

```text
build/aggfix/stage3/simple native-build ... \
  --cache-dir build/native_probe/phase3_cache \
  --entry examples/06_io/ui/wm_full_stack_demo.spl
```

After normalizing the multiline expressions rejected by that older parser,
the focused GPOS source-entry build and the full WM closure now complete. The
cold full closure built 512 modules; the final incremental pass compiled 3 and
reused 509 cached modules. No full bootstrap or Phase 2 retry was run.

The existing `SIMPLE_LINK_OBJECTS` final-link hook supplies the GLFW and
miniaudio provider objects. The resulting executable defines its active
`rt_glfw_*` and `rt_audio_*` symbols and no longer depends on an ineffective
preload for compiler-generated extern slots.

Two live native faults in theme parsing were the documented erased-result
`.to_i32()` misdispatch into `Px.to_i32()`. Typed `i64` intermediates with
`as i32` now carry those conversions. The third and final capped live attempt
passed host/audio initialization and theme loading, then faulted here before a
capturable frame:

```text
ProfileResolver.orientation_changed()
  <- UISession.dispatch()
  <- spl_main()
```

That aggregate-receiver/compiler fault is the current full hosted WM gate.
