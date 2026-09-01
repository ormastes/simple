<!-- codex-research -->
# Typed facet NFR options

## N1 — Safety-first lease model (recommended)

Every invocation acquires a generation-bound lease; unloading revokes before
quiescing.  `try_facet<T>` is no-I/O and allocation-free on a resident indexed
hit/miss.  No executable unmap without an exact loader-owned receipt.

Pros: strongest stale/unload safety.  Cons: per-call pin overhead.  Effort: M.

## N2 — Explicit batch lease

Expose a scoped session lease to amortize pins across hot calls, retaining N1
for one-shot use.

Pros: better hot-path cost.  Cons: more API/escape analysis complexity.  Effort: L.

## N3 — Non-unloading modules

Permit typed dispatch but permanently retain dynamic modules.

Pros: simplest and fastest dispatch.  Cons: does not satisfy dynamic-unload
requirements or bounded residency.  Effort: S/M.
