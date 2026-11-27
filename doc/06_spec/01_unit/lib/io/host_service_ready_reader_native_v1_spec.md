# Actual Windows V6 ready-reader prerequisite specimen

Status: **NOT_RUN**, one source-authored actual native scenario in
`test/01_unit/lib/io/host_service_ready_reader_native_v1_spec.spl`.

Required setup: native canonical Windows-thread runner, externally installed
protected V6-only private setup and lease-selected public ready in the actual
Host journal, public canonical setup SHA
and actual native read-profile support. Provide public fixture metadata through
SIMPLE_HOST_AUTH_SETUP_PATH, SIMPLE_HOST_AUTH_SETUP_DIGEST,
SIMPLE_HOST_AUTH_DEPLOYMENT_ROOT and SIMPLE_HOST_AUTH_AUTHORITY_DIGEST.
These variables
contain no key. Missing real setup fails; there is no skip/scripted authority.

The actual reader opens and retains both native files, checks current and
metadata getters, starts close, verifies copied aliases are refused after
invalidation, checks actual selected lease/ready digests, and finishes positive
exact cleanup within16 calls. after_each
retains the returned owner; a new admission cannot overwrite prior unresolved
cleanup. Known closed aliases report the actual closed tombstone.

NOT_COVERED: native ACL/read/close faults, file replacement and cross-thread
faults, live challenge/request/reply MAC exchange, actual listener ownership,
nonce consumption, Host admission, compiler/link and latency/RSS qualification.
The reader is protected-file provenance, not a socket/service authority.

Actual current performs fresh short parent.lease open/read/positive close
before/after; no lease handle is retained across network work on success.
Selector close-fault/replacement/startup-blocking races are NOT_COVERED. A
stale Windows lease can remain after Host close, so this fixture is file
custody, never a live-service or authenticated-network proof.
