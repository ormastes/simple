# Portable HIR fact-generation budget V1

Status: inactive G6 correction evidence. This manual does not grant semantic
completeness, byte-verifier, object, loader, native, release, or deployment
admission.

Executable source:
`test/01_unit/compiler/cache/portable_hir_fact_generation_budget_v1_spec.spl`.

## Contract

Fact generation performs a bounded scalar sizing pass before allocating effect
rows, entry keys, signature parts, export descriptors, sort arenas, joined hash
inputs, or copied result arrays. UTF-8 text-key ordering uses the canonical HIR
ordering owner. Reservations follow the graph owner's existing eight-pass key
construction, six-pass frame/join/hash, and typed ordering-arena accounting.

## Boundary scenarios

1. A 2,048-character exported function name fits its exact measured retained
   budget; reducing retained capacity by one byte returns typed `BoundsExceeded`.
2. A 128-parameter exported signature fits its exact measured work budget;
   reducing work capacity by one unit returns typed `BoundsExceeded`.
3. Independent lower-bound assertions ensure long-name and wide-signature work
   cannot regress to descriptor-only accounting.
4. Three exported keys with shared non-ASCII prefixes exercise UTF-8 merge
   comparisons and deterministic export projection under the exact budget.

These scenarios remain non-admissible until run by the qualified self-hosted
runtime and accepted by the independent G6 reviewer.

The final available bootstrap-seed cycle was nonqualifying and stopped at its
`invalid semantic limits` diagnostic for the earlier all-counter-exact fixture.
The fixture now varies only retained/work caps over `standard()` limits, but the
iteration cap forbids a third run. This correction therefore remains RED and
must be rerun by the integration owner on an admitted self-hosted runtime.
