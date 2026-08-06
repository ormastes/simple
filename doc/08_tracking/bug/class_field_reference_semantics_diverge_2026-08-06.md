# Class reference semantics diverge: interpreter value-copies class fields; JIT crashes on optional class field

- **Filed:** 2026-08-06
- **Status:** Open
- **Severity:** High — silently breaks every zero-copy aliasing design (packed-scene writers, arenas)
- **Component:** seed tree-walk interpreter (value-copy) + seed JIT (Option-field nil crash)
- **Found by:** LANE F1 of the render-perf redesign plan (§4.1)

## Contract under test

`class` = identity/reference semantics: assigning a class to a field, array
slot or parameter copies the REFERENCE. `struct` = value semantics. All
engines must agree. Today they do not — this is exactly what forced
`UiSceneNativeWriter` to own growable temporary arrays and row-copy into the
arena instead of writing through a field reference.

## Measured truth table

Fixture: `test/fixtures/repro/compiler/class_identity/class_field_reference_semantics_repro.spl`

Binary: Rust bootstrap seed `bin/release/x86_64-unknown-linux-gnu/simple`
(md5 `ed53cc5f255e269ca27c4cd83b17aef9`) — what `bin/simple` currently is.

| case | JIT (default) | `SIMPLE_EXECUTION_MODE=interpret` |
|---|---|---|
| 1 mutate original, read via field | REF ✅ | **COPY** ❌ |
| 1b mutate via field, read original | REF ✅ | **COPY** ❌ |
| 2 nested (`Outer.inner.cell`) | REF ✅ | **COPY** ❌ |
| 3 class ref in array element | REF ✅ | **COPY** ❌ |
| 4 class as fn parameter | REF ✅ | REF ✅ |
| 6 field re-assignment after construction | REF ✅ | **COPY** ❌ |
| 5 optional class field (`Cell?`) | **CRASH** — `runtime error: field access on nil receiver` + core dump | **COPY** ❌ |

Two distinct defects:

1. **Interpreter value-copies class references everywhere except plain fn
   parameters.** Every field store (construction or re-assignment) and array
   store snapshots the object. Only argument passing aliases.
2. **JIT: an optional class field (`maybe: Cell?`) reads back as nil** —
   `oh.maybe` is nil immediately after `OptHolder(maybe: c5)`, so any access
   dies with "field access on nil receiver" and dumps core. This crashes even
   when the read is hoisted to a local first. Separate defect; filed here
   because the same fixture exposes it.

## Repro commands

```
bin/simple run test/fixtures/repro/compiler/class_identity/class_field_reference_semantics_repro.spl
SIMPLE_EXECUTION_MODE=interpret bin/simple run <same>
```

(Case 6 is ordered before case 5 in the fixture because the JIT crash on 5
would otherwise truncate the table.)

## Localization

- **Interpreter (measured):** Rust seed tree-walk interpreter.
  `src/compiler_rust/compiler/src/interpreter_call/core/class_instantiation.rs`
  builds instances as `fields: Arc::new(fields.clone())` — construction
  snapshots field values into a fresh map, so a class value stored into a
  constructor argument (and, per case 6, a later field store) is copied, not
  aliased. `src/compiler_rust/**` is **out of scope by policy**; no fix
  attempted there.
- **Pure-Simple interpreter** (`src/compiler/interp/mir_interpreter.spl`,
  SetField path) could not be measured: no pure-Simple binary is built in this
  tree. Do not assume it matches either engine; measure before claiming.

## Consequence

The plan's F1 gate ("same corpus, same hashes on every engine") is the
prerequisite for the packed span ABI (F2) and the direct arena writer (F3).
Until the interpreter honors reference semantics, any writer holding a class
field reference to an arena is engine-dependent, and interpreter-mode tests of
zero-copy code are testing a different program.

## Related

- `test/01_unit/compiler/class_reference_semantics_spec.spl` — contract spec.
- Memory: tuple-of-class return does not preserve mutation visibility
  (interpreter) — same family.
- Interpreter Option encoding uses `__tag`; seed `.?` lowers to bool.
