# Network and cryptographic clause/oracle addendum

Status: SOURCE_ACQUIRED / test obligations only. No runtime, entropy-quality,
conformance or branch-coverage PASS. Additive to the merged source/evidence
notes; workers retain their existing requirement IDs. Source editions are pinned
below, not asserted to incorporate every later erratum. All prose is summary;
original RFC copyright notices remain in the private cached texts.

## WebSocket entropy and framing

RFC 6455 section 4.1 item 7 (printed p. 18) requires a random 16-byte nonce for
each connection, base64 encoded in Sec-WebSocket-Key. Section 5.3 (p. 33)
requires a fresh unpredictable 32-bit masking key drawn from strong entropy
for each client frame. A timestamp with only 256 possible states does not meet
that mask requirement. An entropy-source failure must not silently substitute
predictable values: fail-closed propagation is the selected implementation policy,
not a separately quoted RFC error-code requirement.

Independent byte oracle: section 5.7 (p. 38), the published masked Hello frame,
uses mask `37 fa 21 3d` and payload `7f 9f 4d 51 58`; the complete frame begins
`81 85`. Section 5.3 supplies the four-byte repeating XOR rule. This deterministic
fixture proves encoding/unmasking only. Repeated outputs, uniqueness checks or
a statistical sample cannot prove strong entropy. Test the production entropy
owner/failure path and separately assert exact wire bytes under controlled input;
never treat a fixed test mask as acceptable production random generation.

## X448

Reuse pinned RFC 7748. Section 5 (pp. 7–9) specifies scalar/coordinate decoding
and the Montgomery ladder. X448 clears the scalar's lowest two bits and sets
its highest bit; do not apply X25519's distinct top-bit coordinate mask to X448.
Use the exact published 56-byte little-endian inputs and outputs, not hex text
as message bytes or outputs recomputed by Simple's implementation.

Independent oracles: section 5.2 has two X448 scalar/u-coordinate vectors on
printed p. 12; iteration vectors on p. 13 start with k=u=5 and update u to the
previous k after each invocation. Section 6.2 (pp. 15–16) gives Alice/Bob
Curve448 agreement values. Record the selected case and complete expected bytes.
A one-iteration vector proves neither the 1000-iteration case nor branch coverage.
RFC 7748's primitive-level all-zero check is optional; TLS section 7.4.2 of
RFC 8446 and SSH section 3 of RFC 8731 impose their own caller requirements.

## HTTP/1.1 transfer framing

RFC 9112 section 6.1 defines Transfer-Encoding as an ordered coding sequence;
it prohibits applying chunked twice. Section 6.3 item 3 says TE overrides CL,
notes that their coexistence ought to be an error, and requires a forwarding
intermediary to remove CL before forwarding. Rejecting TE+CL outright is the
selected strict policy; do not misquote the RFC as universally requiring rejection.
Item 4 distinguishes final chunked from nonfinal chunked: a response without
final chunked is close-delimited; a request without final chunked requires 400
and connection close. Thus rejecting response gzip or chunked,gzip because the
owner only supports chunked is a capability restriction, not generic RFC invalidity.

RFC 9110 section 5.6.1.2 requires ignoring a reasonable number of empty list
elements; that tolerance is bounded against denial of service. Sections 5.2
and 5.3 govern combining same-name fields and preserving value order. Do not
reduce a coding list to membership in the token chunked. Planned independent
fixtures are hand-constructed from these grammars: duplicate chunked across
one/two fields; case/OWS and bounded empty elements; unsupported coding order;
TE+CL in either header order. These are clause-derived negative/positive fixtures,
not RFC-published KATs. Assertions must check decoded body, consumed bytes,
termination/error and retained bytes for the next message where the API exposes them.

## SSH packet and Curve25519 INIT framing

RFC 4253 section 6 (pp. 7–8) defines packet length excluding its own four bytes
and MAC, a one-byte padding count, payload and padding. Padding is at least
four bytes, at most 255; total pre-MAC length is aligned to max(cipher block
size,8) and at least max(cipher block size,16). Section 6.1 requires support for
the stated 32768-byte payload/35000-byte total limits; 35000 is not a universal
MUST-reject maximum. Section 6.4's MAC covers sequence number and the unencrypted
packet; do not apply that original MAC layout blindly to later AEAD/EtM extensions.

RFC 8731 section 3 incorporates RFC 5656 section 4's INIT layout and mandates
abort for public-key lengths other than 32 bytes (Curve25519) or 56 (Curve448).
RFC 4251 section 5 defines an SSH string as uint32 length followed by bytes.
RFC 5656 section 7.1 defines INIT message number 30. Consequently a Curve25519
INIT payload is 37 bytes: one message byte, four length bytes, 32 key bytes.
This is a grammar deduction, not a quoted published wire vector. Rejecting
trailing payload bytes is the strict whole-message parser policy; distinguish
payload bytes from transport padding and a following packet in the input buffer.
Test short/long string lengths, wrong type, truncation and extra payload bytes
against the actual negotiated-algorithm parser, keeping valid framing controls.

## RSA-PSS finite-size checks

Reuse pinned RFC 8017 sections 8.1.2 (pp. 34–35) and 9.1.2 (pp. 44–45).
The former checks signature width/range before encoded-message verification.
The latter checks encoded length against hash/salt lengths, trailer byte,
forbidden high bits, zero padding, delimiter and recomputed digest. Finite-i64
overflow rejection is an implementation obligation to preserve these mathematical
bounds; the RFC does not prescribe i64 or a Simple-specific error string.
Derive overflow fixtures from the public dimension contract, not from copying
the buggy arithmetic into a test oracle. Positive PSS expected signatures need
a separately pinned published vector or recorded independent signer and explicit
hash/MGF/salt parameters; RFC 8017's verification algorithm is not itself a
published positive-signature vector corpus. Do not claim a signing round-trip
alone is independent conformance evidence.

## Acquisition and reusable original identities

Originals live in `C:/dev/p3new/hash-coverage-20261103/spec-cache`.
Existing RFC 7748/8017/8446 were reused without download; identities remain in
[sources.md](sources.md) and [supplemental_sources.md](supplemental_sources.md).
Seven new RFC Editor texts were downloaded through unique temporary files and
no-overwrite moves. Published editions: RFC 6455 December 2011; RFC 9110/9112
June 2022; RFC 4251/4253 January 2006; RFC 5656 December 2009; RFC 8731 February
2020. Modern unpaginated TXT files use section anchors, not invented page numbers.

| Source | SHA-256 | Retrieved UTC |
|---|---|---|
| [rfc6455.txt](https://www.rfc-editor.org/rfc/rfc6455.txt) | 765775326aee0ecca9b04bde3fd1f52932d498e33e34e428bd61b8a24da0fa3b | 2026-11-03T03:15:02.5722961Z |
| [rfc9112.txt](https://www.rfc-editor.org/rfc/rfc9112.txt) | e4f426bac6206b67fdf9e0da826154f70588db2133a0a86b15cde4ff725d8937 | 2026-11-03T03:15:02.8970272Z |
| [rfc9110.txt](https://www.rfc-editor.org/rfc/rfc9110.txt) | 21c1cdce6ab0e5509b04d84a28000836c7a087cf786efe6f04877ebfff47232a | 2026-11-03T03:15:03.1787063Z |
| [rfc4253.txt](https://www.rfc-editor.org/rfc/rfc4253.txt) | b471173305154f6c66facffcf7a4a25fc5c32765cb30542120be6c20a88f1ed3 | 2026-11-03T03:15:03.4587910Z |
| [rfc8731.txt](https://www.rfc-editor.org/rfc/rfc8731.txt) | 26dcf1e8481d83e0b2403e41df47df3fb08cae154d1e464631a23b3cd025f9d1 | 2026-11-03T03:15:03.7595682Z |
| [rfc5656.txt](https://www.rfc-editor.org/rfc/rfc5656.txt) | 0cc84636afaf4860f97271b5b411be0393f71544d3c219f25df2d78201a4949a | 2026-11-03T03:15:34.7008950Z |
| [rfc4251.txt](https://www.rfc-editor.org/rfc/rfc4251.txt) | 23a5052796d29edc2f0ff4f5be557df244544d129cfc26ed51971a6485eff4ef | 2026-11-03T03:15:35.6383410Z |
