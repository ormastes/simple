# Canonical scalar failure publication

Executable owner:
`test/01_unit/compiler/frontend/flat_pool_canonical_failure_publication_spec.spl`.
Requirement: REQ-FLAT-POOL-TRUNCATION-001.

Four scenarios feed canonical readers a valid first value and the noncanonical
integer `01`. Integer and boolean decoding, each with allocating and retained
storage variants, must reject the second value before appending it.

The integer scenarios require `[7]`; the boolean scenarios require `[true]`.
All four require `reader.ok=false`. In particular, rejection must not publish
the reader's integer fallback zero as a valid false boolean.

Cached Stage 1 source-inline diagnostic: 4 executed, 4 passed, zero failed.
Admitted self-hosted execution and native qualification remain pending. The
source-inline diagnostic includes the actual repaired owner definitions, but
does not qualify module import resolution or bootstrap release admission.
Receipt/source hashes: `build/phase1-flat-pool-truncation-20261011`.
