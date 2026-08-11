# Bug: backend type_mapper composite-type strategy dispatch accesses
`.kind` on a value of type `function`

**Status:** FIXED 2026-08-09 — `InterpreterTypeMapper.map_struct` rewritten to
avoid the buggy pattern; `test/01_unit/compiler/backend/type_mapper_spec.spl`
is 4/4 green.

**Date:** 2026-07-20
**Campaign:** whole-suite 01_unit triage (fix_guide.md)
**Severity:** Genuine compile-time semantic error — 1 of 4 examples blocked

## Symptom

```
BIN=/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple
SIMPLE_RUST_SEED_WARNING=0 timeout 90 "$BIN" test \
  test/01_unit/compiler/backend/type_mapper_spec.spl \
  --no-session-daemon 2>&1 | sed 's/\x1b\[[0-9;]*m//g' | grep -A2 '✗'

✗ handles composite types using each backend strategy
  semantic: undefined field 'kind': cannot access field on value of type 'function'
```

3 of 4 examples pass ("maps pointers according to backend memory model",
"keeps target-sensitive size and signature helpers stable", and one other);
only "handles composite types using each backend strategy" fails.

## Root-cause hypothesis (not verified against source)

The example likely iterates a table of `(backend, type)` pairs or passes a
per-backend strategy closure where a `MirType`/similar value with a `.kind`
field was expected, but somewhere in that path a bare function value (e.g.
a strategy closure itself, or the result of a lookup that should have
returned a type but returned a function reference instead) is being passed
where a type value was expected, and `.kind` is then accessed on it.

## Reproduction

`test/01_unit/compiler/backend/type_mapper_spec.spl`, example "handles
composite types using each backend strategy".

## Root cause (confirmed)

`src/compiler/70.backend/backend/interpreter_type_mapper.spl`, method
`map_struct`, used:

```
val field_types = fields.map("{_.0}: {self.map_type(_.1)}")
```

The `_` placeholder-lambda promotion for `.map(...)` mis-binds the *nested*
`self.map_type(_.1)` call embedded inside the string interpolation: instead
of evaluating `_.1` against the outer `.map` element and passing the
resulting `MirType` to `map_type`, it wraps `_.1` as its own closure and
passes that function value into `map_type`, which then panics accessing
`.kind` on a `function`. This interpolated-placeholder pattern
(`"{_.field}"` referencing the map element inside a nested call inside a
string literal) had exactly one call site in the whole `70.backend/` tree;
every sibling mapper (e.g. `llvm_type_mapper.map_struct`) instead uses the
working bare-closure form `fields.map(self.map_type(_.1))`.

## Fix

Rewrote `map_struct` to use an explicit `for` loop building `"{name}:
{ty_str}"` per field instead of the interpolated-placeholder `.map(...)`
call, matching the pattern used by the other backends' `map_struct`
implementations. Isolated regression check (temporary per-assertion spec,
removed after use) confirmed the interp `map_struct`/`map_union`/tuple
compositions all pass individually and together; the full spec file is now
4/4 green.

Note: the underlying general defect — `_` placeholder-lambda promotion
inside a nested call embedded in a string interpolation can bind to the
wrong scope — is not otherwise characterized or fixed here; only this one
call site is confirmed to hit it, and it has been rewritten to avoid the
pattern rather than to exercise it.
