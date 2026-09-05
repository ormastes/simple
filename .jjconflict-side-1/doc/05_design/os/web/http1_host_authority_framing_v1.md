# SimpleOS HTTP/1.1 Host Authority Framing V1

## Scope

The filesystem-launched server accepts private HTTP/1 traffic through
`Http1RequestFrameOwner`. Its deliberately strict deployment rule requires
HTTP/1.1 requests to contain one Host field whose trimmed value is non-empty;
the existing shared singleton policy rejects duplicates. HTTP/1.0 retains its
optional-Host behavior. This phase does not validate Host grammar, bind Host
to a configured authority, or prove request-target/Host consistency. It does
not claim general-purpose HTTP/1.1 conformance or TLS, HTTP/2, WebSocket,
HTTP/3, or QUIC production ownership.

## Owner and invariant

The private incremental owner records the validated request version and two
Host observations while it already scans header bytes. At the empty header
line it first delegates duplicate-singleton and body framing policy to the
shared `headers_decision`, then rejects HTTP/1.1 when Host was absent or its
trimmed value was empty. The owner exposes no resumable or forgeable state.

Header-name matching compares the four ASCII bytes case-insensitively after
the existing field-token validation. It performs no lowercase allocation and
does not rescan the retained headers. Complexity remains O(request bytes),
with O(1) extra state and the existing bounded retained-byte policy.

## Acceptance source

RFC 9112 section 3.2 supplies the Host presence and duplicate baseline; it also
allows an empty Host for undefined target authority. The filesystem server's
deployment rule deliberately rejects an empty trimmed value without claiming
that this establishes valid or configured authority. The focused acceptance
seam is
`frame_http1_fragments_owned_for_test` in
`test/01_unit/os/apps/servers_user/http1_request_frame_owner_spec.spl`:

- missing or whitespace-only HTTP/1.1 Host rejects with 400;
- a mixed-case non-empty Host completes;
- HTTP/1.0 without Host completes;
- duplicate Host remains rejected by the shared singleton policy.

Runtime verification is intentionally pending.
