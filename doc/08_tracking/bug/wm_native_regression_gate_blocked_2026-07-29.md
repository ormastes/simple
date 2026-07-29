# WM Native Regression Gate Blockers — 2026-07-29

## Self-hosted source closure

The WM system and GUI shortcut specs initially stopped because the
repository-wide source closure reached:

```text
src/lib/skia/feature/shaper/ot_layout_shaper.spl
Unexpected Dedent
```

The conditional at that location has now been normalized to the older Phase-3
grammar. An isolated shaper closure advanced to the same old-parser dedent
class in `ot_layout_gpos_data.spl`; two bounded attempts were used. The full WM
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

`runtime_glfw.c` compiles and its loader self-check passes, but this host has no
loadable GLFW library or live display. This proves fail-closed loading only,
not the required visual/input runtime evidence.

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

After normalizing two multiline expressions rejected by that older parser,
the bounded third attempt reached the unrelated Skia shaper
`Unexpected Dedent`. The first shaper form is now normalized, while an
isolated probe exposes a second `ot_layout_gpos_data.spl` dedent. No full-WM
retry, full bootstrap, or Phase 2 retry was run.
The retained diagnostic is:

```text
build/native_probe/wm_full_stack_demo_phase3.log
```
