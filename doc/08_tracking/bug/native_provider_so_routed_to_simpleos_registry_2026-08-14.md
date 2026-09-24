# Native provider `.so` routed to the SimpleOS registry
## Closed 2026-09-16 — ...expose `simple_provider_query_v1`. ## Fix - Add bounded raw-text host runtime entry points

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

## Status

Fixed in source with a real shared-object regression fixture. The hosted ABI
self-check passes. Pure-Simple native end-to-end reverification remains OPEN:
the admitted Linux Stage 2 compiler stops earlier in
`provider_query_wire.spl` with an unrelated HIR field-inference error, so this
lane does not fabricate an invocation PASS.

## Reproduction

The Pure Simple provider dispatch runner admitted a real shared object but
failed with `provider-admission-failed:query-symbol-missing`.

`src/os/posix/dynlib.spl` routed ELF shared objects through the SimpleOS kernel
dynamic-library registry. That registry cannot perform hosted `dlopen`/`dlsym`,
so a valid host `.so` could never expose `simple_provider_query_v1`.

## Fix

- Add bounded raw-text host runtime entry points for open, symbol lookup, and
  close.
- Route ELF `.so` artifacts through those hosted entry points.
- Keep SMF artifacts on the SimpleOS registry path.
- Keep provider query wire encoding and provider implementation in Pure Simple.
- Reject zero and negative host handles before constructing a library carrier.
- Preserve `.smf` routing through the SimpleOS kernel registry while native
  `.so`/`.so.N`/`.dylib` artifacts use only the hosted loader.
- Classify only a basename with a complete native suffix (`.so`, numeric
  `.so.N`, or `.dylib`) rather than treating any absolute path as ELF.

The runtime boundary performs only the platform loader operation. Composition,
admission, query descriptors, dispatch, and response encoding remain Pure
Simple.

## Evidence and remaining gate

Rust compiler/runtime source checks, C syntax checking, the environment-runtime
audit, and diff checks pass. The already-started end-to-end criterion exhausted
the mandatory three-cycle cap while revealing a second provider dependency on
`str.to_bytes`; the provider now uses the canonical Pure Simple byte-native CLI
result encoder. Its size predicate is tested without allocating a megabyte-size
fixture, avoiding an interpreter-performance regression in the regression test.
The regression spec
`test/01_unit/os/posix/dynlib_host_facade_boundary_spec.spl` opens a compiled
`.so`, resolves a real symbol, closes it, rejects non-positive handles, and
proves `.smf` retains its distinct format classification. The executable verifier
`scripts/check/check-native-provider-so-route.shs` builds the real CLI provider
fixture and Pure-Simple dispatch runner, checks the lifecycle receipt, and
records elapsed startup time plus max RSS. It fails closed when no admitted
runtime is supplied.

On 2026-09-22, `scripts/check/check-cli-provider-v1-host.shs` passed and the
provider host self-check measured `elapsed_s=0.00 max_rss_kib=1076`. This is
host-boundary evidence, not a Pure-Simple invocation receipt. The native runner
build was attempted once with the admitted Linux Stage 2 compiler and 12 jobs;
it failed before code generation at
`provider_query_wire.spl: _push_digest_v1: cannot infer ... word0`. Do not claim
invocation, startup-impact, or native max-RSS PASS until the post-bootstrap
runtime executes `check-native-provider-so-route.shs` successfully.

TODO(deferred-environment): after Linux Stage 2/3 admission, run
`scripts/check/check-native-provider-so-route.shs` once in a bounded session and
record the invocation, startup-time, and max-RSS receipt here.
