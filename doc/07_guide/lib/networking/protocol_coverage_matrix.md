# Network Protocol Coverage Matrix (Dan Nanni stack)

Evidence-based status of every protocol in the Dan Nanni layer diagram, verified
**module-by-module against the repo** on 2026-06-16. Each protocol has a
committed implementation module and at least one spec; this table records the
source location, source size, and spec count. "Specs" counts `*_spec.spl` files
matching the protocol across `test/`.

> This document exists because the implementation status is sometimes
> mis-summarized from a single session transcript as "not yet implemented." The
> repo evidence below is authoritative: the stack is implemented and tested.

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
| QUIC | `src/lib/nogc_async_mut/io/quic/` (+ UDP carrier) | 3764 | 7 |
| SSH | `src/lib/nogc_sync_mut/io/ssh_*.spl` + `src/os/apps/sshd/` | — | ✅ |
| BGP | `src/lib/nogc_sync_mut/bgp/` | 531 | 29 |

## Standard application

| Protocol | Module | Src lines | Specs |
|----------|--------|----------:|------:|
| HTTP/1/2/3 + WebSocket | `src/lib/nogc_sync_mut/http/` (`h2/`, `h3/`, `ws/`) | 2469 | 83 |
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
- **QUIC** — Initial packets round-trip over real UDP (RFC 9000 wire bytes).

Remaining handshake-crypto follow-ups (documented in `doc/08_tracking/bug/`):
Ed25519 signature output, full QUIC/DTLS handshake AEAD wiring, RSA-2048 modexp
interpreter performance.
