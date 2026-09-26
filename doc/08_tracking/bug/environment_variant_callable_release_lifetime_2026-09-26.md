# Environment variant callable can outlive its native mapping

**Status:** Candidate source fix on `feature/dynload-callable-lifetime`; runtime verification and release qualification pending a source-matched pure-Simple runner.
**Scope:** `src/lib/nogc_sync_mut/composition/environment_variants/callable_map_v1.spl` and `session_callable_adapter_v1.spl`.

## Evidence

At baseline `7b3cfd5a280`, `_map_native` saves both a raw `native_fptr` and `native_handle` in
`VariantCallableV1`. `variant_callable_invoke_v1` calls `native_fptr` whenever
it is positive. `variant_callable_release_v1` closes `native_handle` without
changing the callable or revoking aliases. `session_callables_release_v1`
iterates copies in an array and exposes the same path. A second release may
close the same handle twice; an invoke after release may jump into unloaded
code. The current native fixture calls release only once and never invokes
afterward, so its existing assertions do not cover either failure.

Simple classes have value semantics (`doc/07_guide/quick_reference/
syntax_quick_reference.md`, capability-group rules). Clearing fields on one
copy cannot revoke another copy. The current deterministic `mapping_handle`
and `callable_handle` values are also shared by independent loads of the same
artifact, symbol, and provider generation; they cannot serve as unique mutable
lifetime keys without a distinct per-load identity.

## Required correction

Give each mapping a single authoritative owner and a unique lifetime identity.
Invoke must acquire a live use before reading the function pointer; retirement
must reject new uses and close exactly once after existing uses finish. The
candidate owner defers close to the final in-flight invocation if necessary,
so release reports accepted revocation rather than synchronous close. Copies
of a callable must resolve through the same owner so release invalidates every
copy. Avoid a permanent per-load atomic allocation without an owner that can
reclaim it. Preserve placement, ABI, artifact, and generation admission checks.
A stale callable must return a typed refusal without entering foreign code.

## Acceptance evidence

Run the native fixture with a source-matched pure-Simple runner and verify:

1. Two independently mapped copies with equal artifact metadata remain distinct lifetimes.
2. Double release closes the mapping once and gives a defined second result.
3. Invoke through every retained copy after release returns a typed refusal.
4. Release concurrent with an in-flight invocation revokes new admissions; the final admitted invocation closes the mapping when it finishes.
5. Failed multi-facet bind releases every mapping exactly once, and the successful session retirement path revokes every callable.

No current source check or metadata receipt proves these outcomes. Do not mark
the native dynload workstream release-qualified until this gate passes.

The candidate serializes a bounded registry with one mutex and looks up the
identity linearly on every native invocation. That is a correctness staging
point, not evidence for Stage 2's allocation-free, lock-free hot dispatch or
latency/RSS targets. Those targets require an independently measured indexed
owner or another safe fast path before production promotion.
