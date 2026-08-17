# Browser Fetch redirect deadline reset

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Status

Source fix and deterministic SSpec implemented. Runtime PASS remains blocked by
the current pure-Simple source-discovery failure.

## Root cause

`FetchEngine.fetch_with_redirect` created a new `H1Client.request` for every
redirect. Each H1 request created `now + 5000 ms`, so the 20-redirect ceiling
permitted roughly 105 seconds of aggregate DNS/connect/TLS/write/read work.
CORS preflight also created an independent H1 budget.

## Fix

`FetchEngine.fetch` now creates one absolute deadline. Redirect recursion,
CORS preflight, and H1 transport receive that unchanged value. Existing
single-hop callers retain a five-second default. Deterministic mock latency
uses virtual monotonic time and never sleeps or opens a socket.

The DNS facade still exposes only blocking `browser_dns_lookup(hostname)`;
there is no remaining-deadline argument to interrupt that lookup. H1 checks the
same deadline immediately afterward, but a DNS call itself can overrun it.
That pre-existing runtime/facade limitation remains an explicit open production
evidence blocker rather than being hidden by this redirect-reset fix.

## Evidence

- Executable SSpec:
  `test/01_unit/lib/gc_async_mut/gpu/browser_engine/fetch_deadline_spec.spl`
- Manual:
  `doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/fetch_deadline_spec.md`
- Cases: aggregate timeout across HTTP/HTTPS, success within budget, and the
  unchanged 20-redirect ceiling.

The single allowed Stage 2 native-build stopped during source discovery at the
pre-existing `src/lib/gc_async_mut/gpu/browser_engine/security/origin_policy.spl`
dedent parse failure, before this lane was compiled. The deployed full CLI
attempted forbidden Rust-seed delegation; do not rerun either unchanged.

The retained standalone fixed pure Phase 2 docgen
(`f9a5abc6bd1333de4c298c85dea03eb579e155e100eccdca5200c696051c489f`)
generated the mirrored manual as 1/1 complete with 0 stubs.
The only remaining documentation-quality warning is the allowed 19-line
recommendation (100+ suggested); it is not runtime evidence.
