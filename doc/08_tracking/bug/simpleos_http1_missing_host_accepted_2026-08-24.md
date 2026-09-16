# SimpleOS HTTP/1.1 missing Host accepted

## Finding

The filesystem-launched production server's incremental request owner accepted
HTTP/1.1 requests with a missing or empty `Host` field. Duplicate Host fields
were already rejected by shared header policy, but presence was not enforced.
Empty Host is valid for some authority-less RFC request targets; the
filesystem server intentionally applies the narrower fail-closed rule that the
trimmed value be non-empty. This change does not validate Host grammar,
configured authority, or request-target consistency.

## Resolution state

Implemented, unverified. `Http1RequestFrameOwner` now records request version
and Host presence/value validity during its existing scan and rejects missing
or empty HTTP/1.1 Host at end-of-headers. HTTP/1.0 behavior is unchanged.

## Acceptance

The focused source scenarios live in
`test/01_unit/os/apps/servers_user/http1_request_frame_owner_spec.spl` and bind
missing, empty, mixed-case, HTTP/1.0, and duplicate cases. No tests, builds, or
runtime verification were run in this phase; keep this record open until that
focused spec passes with an admitted Pure-Simple runtime.
