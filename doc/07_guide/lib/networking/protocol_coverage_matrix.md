# Network Protocol Coverage Matrix (Dan Nanni stack)

Evidence-based status of every protocol in the Dan Nanni layer diagram. Module
and spec presence proves only the named layer; it does not prove an
authenticated live service. Wire codecs, state profiles, transport integration,
and production readiness are reported separately.

> A protocol must not be advertised from a source/spec count alone. In
> particular, HTTP/3 remains blocked until an authenticated QUIC-TLS handshake
> installs application keys and behaviorally carries request/response data.
> Typed bounds and integration rules are in
> [Modern web protocol profiles](modern_web_protocol_profiles.md).

## Layer 3 — Internet / addressing

| Protocol | Module | Src lines | Specs |
|----------|--------|----------:|------:|
| IPv4 | `src/os/services/netstack/ipv4.spl` | 332 | ✅ (added 2026-06-16) |
| IPv6 | `src/os/services/netstack/ipv6.spl` | 228 | ✅ |

## Layer 3 control / multicast signaling

| Protocol | Module | Src lines | Specs |
|----------|--------|----------:|------:|
| ICMP | `src/os/services/netstack/icmp.spl` | 209 | ✅ |
| ICMPv6 | `src/os/services/netstack/icmpv6.spl` | 292 | ✅ |
| IGMP | `src/os/services/netstack/igmp.spl` | 297 | ✅ |
| MLD | `src/os/services/netstack/mld.spl` | 249 | ✅ |

## Routing & security infrastructure

| Protocol | Module | Src lines | Specs |
|----------|--------|----------:|------:|
| OSPF | `src/lib/nogc_sync_mut/ospf/` | 400 | ✅ |
| RIP | `src/lib/nogc_sync_mut/rip/` | 259 | 128 |
| IPsec | `src/lib/nogc_sync_mut/ipsec/` | 332 | ✅ |

## Transport (core pipes)

| Protocol | Module | Src lines | Specs |
|----------|--------|----------:|------:|
| TCP | `src/lib/nogc_sync_mut/tcp/` + `io/tcp.spl` (real FFI) | 1295 | 19 |
| UDP | `src/os/services/netstack/udp.spl` + `io/udp.spl` | 290 | 14 |
| SCTP | `src/os/services/netstack/sctp.spl` | 461 | ✅ |
| DCCP | `src/os/services/netstack/dccp.spl` | 247 | ✅ |

## Cryptographic & session

| Protocol | Module | Src lines | Specs |
|----------|--------|----------:|------:|
| TLS | `src/lib/nogc_sync_mut/tls/` (+ `io/tls_stream.spl` over real TCP) | 2588 | 82 |
| DTLS | `src/lib/nogc_sync_mut/dtls/` | 256 | ✅ |
| QUIC wire/profile (live TLS blocked) | `src/lib/nogc_async_mut/io/quic/` (+ UDP carrier) | 3764 | 7 |
| SSH | `src/lib/nogc_sync_mut/io/ssh_*.spl` + `src/os/apps/sshd/` | — | ✅ |
| BGP | `src/lib/nogc_sync_mut/bgp/` | 531 | 29 |

## Standard application

| Protocol | Module | Src lines | Specs |
|----------|--------|----------:|------:|
| HTTP/1 + WebSocket; HTTP/2 typed framing/profile; HTTP/3 bounded framing only | `src/lib/nogc_sync_mut/http/` + async facades | 2469 | 83 |
| DNS | `src/lib/nogc_sync_mut/dns/` (+ `wire.spl` RFC 1035) | 1178 | ✅ |
| NTP | `src/lib/nogc_sync_mut/ntp/` | 333 | 10 |
| RTP | `src/lib/nogc_sync_mut/rtp/` | 303 | ✅ |
| SNMP | `src/lib/nogc_sync_mut/snmp/` | 560 | ✅ |
| SIP | `src/lib/nogc_sync_mut/sip/` | 707 | 5 |
| LDAP | `src/lib/nogc_sync_mut/ldap/` | 1147 | ✅ |
| VNC | `src/lib/nogc_sync_mut/vnc/` | 626 | ✅ |
| RDP | `src/lib/nogc_sync_mut/rdp/` | 685 | ✅ |
| SMTP | `src/lib/nogc_sync_mut/smtp/` | 898 | ✅ |
| IMAP | `src/lib/nogc_sync_mut/imap/` | 459 | ✅ |
| POP3 | `src/lib/nogc_sync_mut/pop3/` | 396 | ✅ |
| DHCPv6 | `src/os/services/netstack/dhcpv6.spl` | — | ✅ |
| DHCPv4 | `src/os/tools/net/dhcp_client.spl` | — | — |

## Secure wrappers (X-over-TLS)

`SMTPS / IMAPS / POPS / HTTPS / LDAPS` are each `<proto>/secure.spl` composing
the cleartext protocol session over the TLS layer (ports 465/993/995/443/636).

## End-to-end transport status (2026-06-16)

The protocol *logic* is implemented and unit-tested above. End-to-end on real
sockets:

- **TCP** — real FFI (`io/tcp.spl`, `rt_io_tcp_*`/`native_tcp_*`); loopback
  smoke test passes.
- **UDP** — real FFI (`native_udp_*` + `rt_io_udp_*` interpreter shims added
  2026-06-16); loopback passes.
- **TLS** — record layer (AES-128-GCM) runs over real TCP (`io/tls_stream.spl`),
  byte-exact round-trip + auth-fail reject. **X25519 ECDHE** key agreement
  fixed 2026-06-16 (RFC 7748 vectors). AEAD (AES-GCM, ChaCha20-Poly1305),
  HKDF/HMAC, RSA PKCS#1, X.509 DER parser all present and KAT-verified.
- **HTTP/2 profile** — bounded typed parsing distinguishes incomplete,
  rejected, and ignorable extension frames; SETTINGS and WINDOW_UPDATE limits
  are checked. This row does not claim a production TLS/ALPN service.
- **HTTP/3 framing** — bounded frame and atomic SETTINGS parsing are available.
- **QUIC** — long-header structure and Initial key primitives are implemented,
  but authenticated live transport is **BLOCKED**. Plaintext Handshake/1-RTT
  data cannot authorize state transitions or application emission.

Remaining handshake-crypto blockers are documented in
`doc/08_tracking/bug/quic_h3_transport_tls_blocker_2026-08-20.md`: certificate
and transcript verification, Finished verification, protected packet ingress,
application-key installation, and a live H3 lifecycle. Ed25519 output and
RSA-2048 interpreter performance remain separate crypto follow-ups.
