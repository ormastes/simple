# Bug: seed interpreter — `List<T>()` constructor yields nil receiver

**Date:** 2026-06-12
**Severity:** P2 (blocks interpreter-mode specs for all `core.collections.List`-backed modules)
**Status:** Open

## Symptom

Any interpreter-mode construction of a generic `List` produces a nil receiver;
the first method call fails:

```text
[INFO] JIT compilation failed, falling back to interpreter: semantic: method `push` not found on type `nil` (receiver value: nil)
error: semantic: method `push` not found on type `nil` (receiver value: nil)
```

## Repro

```simple
use core.collections.{List}
var xs = List<i64>()
xs.push(7)
```

`SIMPLE_LIB=src bin/simple run probe.spl` — fails as above (verified 2026-06-12,
stage4 CLI with seed driver). Same failure via `bin/simple test --mode=interpreter`
for any spec touching `compositor/layer.spl` (`LayerTree`), `StackingContext`,
or bare local `List` values.

## Impact

- `test/01_unit/lib/engine/surface_layer_spec.spl` had to restrict itself to
  pure (array-based) assertions; `Scene3DLayer.attach`/`composite_order`
  integration coverage is deferred to the compiled GUI sanity lane
  (`.claude/skills/lib/spipe_ui.md`).
- Any compositor unit spec running in interpreter mode has the same ceiling.

## Notes

- `dict`/array-backed modules are unaffected (audio_bus_spec 30/0,
  fixed_timestep_spec 11/0 pass in interpreter mode).
- Do not work around with compile-mode spec runs: `--mode=native`/`--mode=smf`
  false-green unresolved `std.spec` calls (see memory/compile-mode false-greens,
  2026-04-25).
- Fix belongs in the interpreter generic-class instantiation path; pure-Simple
  first if the constructor lowering lives in `src/compiler`, seed otherwise.
