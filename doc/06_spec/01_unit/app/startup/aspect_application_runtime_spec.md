# Aspect Application Runtime

> Executable source: `test/01_unit/app/startup/aspect_application_runtime_spec.spl`

## Facet method acquisition

The application first-use boundary resolves a published facet, selects its
canonical descriptor method entry, and pins the exact published generation in
one operation. `acquire_published_facet_method(...)` returns the executable
ordinary-SMF method address together with a `FacetGenerationLease`; callers
release that lease through `release_facet_generation_lease(...)`.

The catalog `witness_symbol` remains an inert descriptor identity and method
prefix. It is never called and need not exist in the SMF export table.

PASS requires a positive resolved method address, the expected canonical method
symbol, the exact generation ID, balanced pin counts, and typed rejection of a
second lease release.
