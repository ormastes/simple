# Startup binding publication atomicity

Source: `test/03_system/lib/feature/aspect_activation_atomicity_spec.spl`

Selected requirement: 05-12, selected plan §13.5.

This manual describes the single-owner synchronous loader. Execution and
SPipe generation are **UNRUN** pending a qualified runner; this is an authored
mirror, not a generated PASS report. Cross-thread atomicity is outside this
loader's contract.

## Publish two required routes together

1. Prepare a resident binding before startup activation. Build a real
   three-module aspect pack, install its accepting host offer, and load the
   existing facet through the catalog.
2. Activate both required startup routes.
3. Observe complete publication through real binding lookups. Both new
   facets must have their exact payloads and the same generation, exactly one
   above the previous loader generation. The resident binding keeps its own
   generation.
4. Repeat startup using the cached bindings. Both routes remain available
   and the generation stays unchanged.

## Reject a failing second route without publication

1. Prepare an existing binding and a dangling second route. The first route
   resolves to a real packed module; the second names an absent module.
2. Reject startup when the second routed module is absent. Return zero and
   retain the actual missing-module diagnostic.
3. Observe the unchanged generation and binding registry. Neither startup
   facet is visible, the resident facet retains its payload and generation,
   and no published binding was unloaded as rollback.
4. Recover by activating a corrected catalog. Both startup routes publish
   under exactly one new generation.

## Retain a cached startup route while publishing its peer

1. Acquire the first startup facet before the batch through its real route.
2. Activate the cached route and the new route together. The success count
   includes both.
3. Observe the retained binding and the single new publication. The first
   facet retains its generation and payload; the second facet is visible at
   the next loader generation with its exact payload.

## Activate a catalog with no startup routes

1. Build a catalog containing only a lazy route.
2. Activate an empty startup set. Return zero without an error or generation
   change, and leave the lazy facet unbound.

## Evidence boundary

The exact publisher baseline has no lazy pack callback or concurrent observer
API. External observation is possible after the synchronous call returns.
The design owner accepted before/after boundary scenarios plus source review
of the callback-free commit. No observer seam or unsupported concurrency claim
is introduced. Recoverable route, ABI, negotiation, identity, and generation
failures occur during preparation. Fatal allocator failure has no recoverable
loader API and is outside this returned-result guarantee.
