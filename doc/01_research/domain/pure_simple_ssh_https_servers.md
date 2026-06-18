<!-- codex-research -->
# Domain Research: Pure Simple SSH and HTTPS Servers

## Primary Standards

- SSH transport is defined by RFC 4253. The RFC Editor summary states that SSH
  runs over TCP/IP and provides encryption, server authentication, and integrity
  protection for secure network services: https://www.rfc-editor.org/info/rfc4253/
- TLS 1.3 is defined by RFC 8446. The RFC Editor summary states that TLS lets
  client/server applications communicate in a way designed to prevent
  eavesdropping, tampering, and message forgery:
  https://www.rfc-editor.org/info/rfc8446/
- HTTP semantics are defined by RFC 9110, including common terminology, protocol
  architecture, and the `http`/`https` URI schemes:
  https://www.rfc-editor.org/rfc/rfc9110.html
- HTTP/1.1 message syntax, parsing, connection management, and security concerns
  are defined by RFC 9112: https://www.rfc-editor.org/info/rfc9112/

## Protocol Boundary Implications

SSH and HTTPS both sit above TCP. A "Pure Simple" server can reasonably own
protocol state machines, message parsing, transcript construction, negotiated
algorithms, record framing, authentication decisions, and channel/request
routing, while still delegating actual socket accept/read/write, time, entropy,
and filesystem access to the host OS or SimpleOS.

TLS and SSH cryptography require constant-time primitives, high-quality entropy,
key parsing, and side-channel-safe code paths. If the current runtime provides
cryptographic primitives, they should be declared as crypto primitives rather
than full protocol bypasses. Alpha/beta comparison modes can use existing native
TLS/SSH wrappers as an oracle, but release mode should not silently route
production traffic through those wrappers.

## Minimum Viable Secure Scope

For SSH, the minimum useful server scope is:

- protocol version exchange
- KEXINIT and key exchange
- host-key verification data and exchange hash
- encrypted packet read/write with sequence numbers
- password authentication
- channel open/session handling
- exec command path

For HTTPS, the minimum useful server scope is:

- TCP accept through host adapter
- TLS record parsing and writing
- server handshake for a chosen supported TLS version/cipher suite
- certificate/key loading boundary
- encrypted application-data read/write
- HTTP/1.1 request parsing and response writing

## Standards Risk

TLS 1.3 is the modern baseline, but a full Pure Simple TLS 1.3 server is likely
large because it requires HKDF transcript handling, modern key exchange, AEAD
records, certificate verification surfaces, downgrade rules, and alert handling.
The existing code already has a TLS 1.2 server slice; using that as the first
release-mode supported HTTPS server may be faster, but must be clearly labeled
with supported protocol/cipher-suite limits.

HTTP/1.1 is the practical first HTTP target because RFC 9112 isolates message
syntax and connection management. HTTP/2 or HTTP/3 would add framing, HPACK/QPACK
or QUIC and should be outside the first release-mode slice unless selected.

## Design Constraints for This Repo

- Runtime/SFFI should be treated as host access, not a protocol replacement.
- Existing native SSH/TLS wrappers are useful for alpha/beta comparison or
  compatibility but should be renamed/documented so release mode does not bypass
  Simple protocol code.
- Hosted Linux and SimpleOS should share the same protocol modules and diverge
  only at adapters for sockets, clock, entropy, file/cert/key access, and process
  execution.
- Verification needs both interpreter specs for protocol logic and native/live
  gates for runtime/SFFI adapter behavior.
