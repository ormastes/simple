# Runtime compiler leaked partial object sets on early failure
## Closed 2026-09-16 — Fix section: all post-plan failure returns now cleanup; regression pins 4 exits

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

## Symptom

`compile_runtime_objects` allocates deterministic temporary paths for the whole
runtime source list. A missing later source returned without deleting objects
already compiled earlier in the loop. The zero-object and partial-count
fail-closed returns also omitted cleanup.

## Fix and prevention

All post-plan failure returns now call the existing
`cleanup_runtime_objects(objects)` owner before returning. The focused source
regression in `runtime_compiler_spec.spl` pins all four post-plan exits: missing
source, compiler failure, zero compiled objects, and partial object count.

This fixes the shared hosted C-runtime compiler used by ordinary LLVM,
Cranelift, and Stage4. Runtime/native execution remains pending under this
session's explicit static-only restriction.

