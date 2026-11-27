# Actual Windows V6 setup-publication administrative specimen

Status: **NOT_RUN**, one source-authored actual native scenario in
`test/01_unit/lib/io/host_service_auth_setup_native_v1_spec.spl`.

This explicit administrative fixture would publish an immutable private setup
if run. It requires a native canonical Windows thread, actual protected parent,
OS CSPRNG and an operator-selected fresh unpublished target supplied by
SIMPLE_HOST_AUTH_FRESH_SETUP_TARGET. No native execution or provisioning was
performed here. Missing setup/collision fails; no fake native owner or success.

The source drives actual open/step through at most64 phases, checking positive
setup publication, canonical UID/public digest, completed cleanup and closed
alias idempotence. after_each retains and retries actual cleanup; published
immutable files are never automatically deleted or overwritten by the test.
The operator owns final artifact recovery/removal under deployment policy.

NOT_COVERED: native partial stage/write/flush/publish/adopt/readback/close faults,
uncertain or collision recovery execution, server ready publication/listener
composition, private setup lifetime across service restart, actual MAC network
exchange, compiler/link/platform behavior and latency/RSS. Pure shape checks
and a generator label do not independently attest entropy against a trusted
administrator; the actual source chain opens protected roots before OS random.
