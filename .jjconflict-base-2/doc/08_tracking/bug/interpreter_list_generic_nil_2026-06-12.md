# Bug: seed interpreter — `List<T>()` constructor yields nil receiver

**Date:** 2026-06-12
**Severity:** P2 (blocks interpreter-mode specs for all `core.collections.List`-backed modules)
**Status:** Source fixed in Rust-seed and pure-Simple interpreters;
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

## Resolution

Generic-call parsing now preserves `List<i64>()` as a call to `List`, and the
Rust class-instantiation path honors the object returned by an implicit
zero-argument `new`. The pure-Simple core interpreter now mirrors that rule:
an uppercase declared type called with no source arguments dispatches an
existing static `Type__new`, while the field-bearing call inside `new` still
falls through to ordinary construction. `List.new()` therefore returns
`List(items: [])` instead of a value whose `items` field is nil.

The pure-Simple fix also registers methods nested in parser-generated
`DECL_IMPL` blocks for both the current module and lazily loaded modules. A
small active-constructor stack prevents `Type.new()` implementations that
return `Type()` from recursively invoking themselves; it does not suppress a
different type's constructor.

`test/01_unit/lib/core/list_constructor_hardening_spec.spl` now exercises the
original spelling directly, pushes one item, and reads it back. This replaces
the earlier source scan that merely banned the crashing spelling. The focused
core CI lane now executes this exact spec in interpreter mode and the bootstrap
portability audit pins both its workflow triggers and command. First CI
execution is pending. The core-interpreter integration program also contains a
local generic `Bucket<T>()` sentinel and CI requires its `Fail: 0` / `ALL TESTS
PASSED` summary, covering the pure-Simple evaluator rather than only the Rust
seed's class-instantiation implementation.

## Notes

- `dict`/array-backed modules are unaffected (audio_bus_spec 30/0,
  fixed_timestep_spec 11/0 pass in interpreter mode).
- Do not work around with compile-mode spec runs: `--mode=native`/`--mode=smf`
  false-green unresolved `std.spec` calls (see memory/compile-mode false-greens,
  2026-04-25).
- Fix belongs in the interpreter generic-class instantiation path; pure-Simple
  first if the constructor lowering lives in `src/compiler`, seed otherwise.
- 2026-06-22: owned `src/` uses of the crashing direct constructor spelling
  `List<T>()` were rewritten to `List<T>.new()` as a temporary workaround.
