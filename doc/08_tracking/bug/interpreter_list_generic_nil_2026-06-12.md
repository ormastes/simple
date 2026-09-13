# Bug: seed interpreter — `List<T>()` constructor yields nil receiver

## Closed 2026-09-13 — FIXED: `List<T>()` now usable; missing field default was the residual cause

### Regression specs (added 2026-09-13)

- `test/01_unit/lib/core/list_zero_arg_ctor_spec.spl` — reproducing +
  generalization, 7/7 green. **measured** controlled A/B on this host:
  `items: [T]` (no default) leaves `push` a silent no-op (`len()==0`), while
  `items: [T] = []` gives `len()==1`. Harness control-tested (a deliberately
  wrong expected value does fail), so the pass is not vacuous.

- **measured (before)** On the current seed the filed symptom was already gone (no
  `method push not found on type nil`), but a silent successor remained:
  `var xs = List<i64>(); xs.push(7); xs.push(9)` gave `after len=0`, `get0=nil` — pushes
  vanished. `List.new()` and `List<i64>(items: [])` were fine, so only the zero-arg
  direct constructor was broken: `items` was left nil and every mutation was a no-op.
- **fix** Gave the field an explicit default in both copies of the class:
  `items: [T] = []` in `src/lib/core/collections.spl:5` and
  `src/lib/common/core/collections.spl:8`. No other change; `src/lib` needs no rebuild.
- **measured (after)** Same program now prints `empty len=0`, `after len=2`, `get0=7`;
  `List<i64>(items: [])` and `List.new()` still print `1` and `2`.
- Binary used: Rust seed v1.0.0-rc.1 (Windows). Not re-checked on a self-hosted binary.


**Date:** 2026-06-12
**Severity:** P2 (blocks interpreter-mode specs for all `core.collections.List`-backed modules)
Status: closed 2026-09-13 (was: **Status:** Source fixed in Rust-seed and pure-Simple interpreters;)
direct-constructor execution pending

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
- 2026-06-22: owned `src/` uses of the crashing direct constructor spelling
  `List<T>()` were rewritten to the working `List<T>.new()` form, covering the
  compositor modules called out above. Guarded by
  `test/01_unit/lib/core/list_constructor_hardening_spec.spl`. Root interpreter
  constructor lowering remains open.
