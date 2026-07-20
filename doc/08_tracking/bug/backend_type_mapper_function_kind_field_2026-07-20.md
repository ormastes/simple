# Bug: backend type_mapper composite-type strategy dispatch accesses
`.kind` on a value of type `function`

**Status:** OPEN — filed, not fixed (source not read in depth)

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

## Suggested follow-up

Read the example body and the `type_mapper` composite-type dispatch it
exercises (likely `src/compiler/70.backend/backend/type_mapper.spl` or
similar) to find where a function value flows into a `.kind` access instead
of the intended type value.
