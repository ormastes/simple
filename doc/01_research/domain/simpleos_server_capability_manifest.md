# SimpleOS server capability manifest — domain research

Protocol negotiation is an interoperability claim, not a wishlist. ALPN binds
the selected application protocol to a TLS connection, while HTTP/2 assigns
`h2` to its TLS deployment. An implementation should therefore advertise only
protocols whose framing, session, and request owners are reachable on the live
server path. Unknown identifiers must fail closed.

SSH provides the authenticated transport and connection layers; SFTP is a
separate subsystem negotiated inside an SSH session. Server readiness does not
by itself prove authenticated SFTP reachability, so the two capabilities need
independent predicates and evidence identities. Likewise HTTP/3 requires QUIC,
and WebTransport requires its own reachable session owner; HTTP/1.1 or HTTP/2
support cannot be promoted into either claim.

For SimpleOS this supports a small production projection: `http/1.1` and `h2`
after live HTTP identities exist, `ssh` after daemon readiness, and `sftp-v3`
only after authenticated subsystem readiness. The shared manifest validator is
the final fail-closed boundary.

References:

- [RFC 7301: TLS Application-Layer Protocol Negotiation](https://www.rfc-editor.org/rfc/rfc7301)
- [RFC 9113: HTTP/2](https://www.rfc-editor.org/rfc/rfc9113)
- [RFC 9000: QUIC](https://www.rfc-editor.org/rfc/rfc9000)
- [RFC 4254: SSH Connection Protocol](https://www.rfc-editor.org/rfc/rfc4254)
- [SSH File Transfer Protocol draft](https://datatracker.ietf.org/doc/html/draft-ietf-secsh-filexfer-02)
