# TODO: unit-system-semantic-wiring

**Filed:** 2026-04-24
**Parent feature:** `unit-system-consolidation` (shipped as WIP)
**Blocks:** AC-5 (composite runtime), AC-8 (integration tests) of the parent feature

## Background

`unit-system-consolidation` delivered the directory tree (`src/unit/simple-lang/` — 31 folders, 331 atomic + 33 composite units), the self-hosted compiler's `UnitRegistry`, postfix literal parsing, import resolution, the `raw_unit` lint, and a migration shim. 7 of 9 ACs green.

Two ACs did not land because the Rust seed compiler (which actually runs user `.spl` programs today) never consults a unit registry at semantic-analysis time. The pure-Simple `UnitRegistry` at `src/compiler/30.types/units/unit_registry.spl` is unreachable from the Rust pass.

## Required work

### 1. Rust-side unit registry
File: create `src/compiler_rust/compiler/src/units/registry.rs` (new module).
- Build a registry at module-load time by scanning `src/unit/simple-lang/**/*.spl` for `class <Name>` + `static fn symbol()/kind()/scale_to_base()/base_unit()` patterns.
- Mirror the Simple-side API: `lookup(symbol)`, `lookup_by_dimensions(dims)`, `convert(value, from, to)`, `dimensions_match(a, b)`.

### 2. Wire into semantic pass
Hook into: `src/compiler_rust/compiler/src/interpreter/expr/literals.rs:305` (numeric-literal unit resolution), `interpreter_method/special/types.rs:87` (`Unit family 'X' not found` error site), `error_factory/codegen_ops.rs:128`.
- When a `NumericSuffix::Unit(s)` is encountered, consult the registry instead of emitting the not-found error.
- Attach the unit type to the HIR literal node.

### 3. Dimension-signature → composite lookup
When `km / h` folds to a `UnitExpression` with `{"length": 1, "time": -1}`, look up the composite name (`velocity` / `kmph`) in the registry and assign that unit type to the result.

### 4. Capitalization policy
The tree uses three conventions inconsistently:
- Lowercase symbol `kmph` (user-facing, literal suffix)
- PascalCase class `Kmph` (type name in `composite/kmph.spl`)
- Ad-hoc `KmphV` (Phase 5 fallback to avoid atomic/composite collision)

Resolve: use `kmph` as the exported symbol, `Kmph` as the wrapper class type. Regenerate collision cases (`Wh_c`, `hp_c`, `Hz_c`, `bpm_c`, `RPM_c`) under the cleaner namespace: `unit.simple-lang.composite.kmph` → symbol `kmph`, type `Kmph`.

### 5. Re-enable AC-5, AC-8 specs
After the registry wires up:
- `test/unit/lib/unit/unit_composite_spec.spl` — flip pending → real assertions
- `test/system/unit_system_integration_spec.spl` — should pass without stubs

### 6. SPipe interpreter-mode limitation (separate)
AC-3 and AC-4 remain "pending" because SPipe's interpreter mode can't execute `it`-block bodies. This is a known architectural limit (see memory: `feedback_interpreter_test_limits`). Compiled-mode spec execution would unpend 29 tests.

## Estimated effort

- Registry module: 1–2 days
- Semantic wiring: 2–3 days
- Dimension lookup: 1 day
- Capitalization cleanup + regen: 0.5 day
- Spec re-enable + verification: 0.5 day

**Total: ~1 week** of focused work. Warrants a dedicated `/dev` pipeline.

## Entry criteria for the follow-up

- Parent feature `unit-system-consolidation` shipped (commit range documented in state file)
- `src/unit/simple-lang/` tree stable
- Pure-Simple `UnitRegistry` at `src/compiler/30.types/units/unit_registry.spl` treated as the canonical spec — mirror its API in Rust
