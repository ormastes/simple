# Stage 2 native build repeats project metadata work per unit

Status: fixed pending verification

## Evidence

A cold Stage 2 build continuously produced valid cached objects but needed over
two hours to process roughly 615 modules. Inspection of
`compile_file_to_object` found five deep clones of immutable project-wide maps,
an all-struct ambiguity scan, and an all-symbol suffix-index build on every
unit.

## Root cause

`ModuleImports` carried the source maps in `Arc`, but the unit compiler cloned
their contents before handing them to HIR and recomputed two derived indexes.
The cost scaled with both project size and compilation-unit count.

## Resolution

Compute field ambiguity and the LLVM suffix index once while constructing the
project import snapshot. Share those indexes and all immutable metadata with
each unit via `Arc::clone`. Keep the per-module `use_map` local because it is
unit-specific.

## Regression evidence

- Ambiguity tests cover equal indexes, disagreeing indexes, and insertion-order
  independence.
- Rust type checking proves every `ModuleImports` producer supplies the shared
  snapshot.
- A subsequent bootstrap run must retain the object cache and demonstrate the
  end-to-end Stage 2/3 outcome; it is not replaced by this focused check.
