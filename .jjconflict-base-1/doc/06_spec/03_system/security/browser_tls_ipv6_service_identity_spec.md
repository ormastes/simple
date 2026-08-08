# Browser TLS IPv6 Service Identity

## Status

Handwritten modern SSpec mirror. Static/offline evidence only; qualified
pure-Simple execution, admitted doc generation, and live certificate/provider
evidence remain pending.

## Requirements

- REQ-WEB-BROWSER-010: canonical URL and Fetch transport targeting
- REQ-WEB-BROWSER-011: HTTPS service identity and no insecure fallback
- REQ-WEB-BROWSER-021: executable SSpec and mirrored manual

## Scope

A canonical IPv6 URL retains brackets in its HTTP authority, for example
`[2001:db8::1]:8443`. The H1 TLS owner now derives `2001:db8::1` as both the
numeric connect address and certificate service identity. It bypasses hostname
DNS only for a canonical bracketed IPv6 literal. DNS hostnames and malformed
bracket forms remain on the existing fail-closed path.

The fix does not change the trust store, certificate-chain validation, expiry
checks, provider implementation, redirect policy, CORS, or HTTP response
handling.

## Scenario: IPv6 authority and TLS identity separation

1. **Parse a bracketed IPv6 HTTPS authority**
   - Confirm canonical scheme, bracketed URL host, port, and wire authority.
2. **Select the bare numeric TLS service identity**
   - Confirm the shared H1 helper removes only the authority brackets and does
     not classify an ordinary DNS hostname as a literal.
3. **Reject malformed bracket forms from the literal fast path**
   - Confirm incomplete, empty, and non-IPv6 bracket values remain excluded.
4. **Preserve bracketed authority on the HTTP wire**
   - Confirm the request line and canonical bracketed `Host` field while a
     caller-supplied hostile Host field remains suppressed.

## Evidence boundary

Executable source:
`test/03_system/security/browser_tls_ipv6_service_identity_spec.spl`.
The SSpec deliberately performs no DNS, socket, TLS-provider, or live
certificate operation. It proves deterministic target preparation and H1 wire
authority only. Live platform-trust, chain, expiry, SAN/IP identity, deadline,
and cleanup evidence remains open.
