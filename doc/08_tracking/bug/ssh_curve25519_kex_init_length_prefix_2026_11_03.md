# SSH Curve25519 INIT framing accepts malformed public-key lengths

Status: OPEN — source-only repair; runtime verification pending.

## Owner and observed source boundary

ssh_transport.spl: ssh_negotiate_algorithms rejects any selected KEX other than curve25519-sha256. ssh_session_kex.spl negotiates before validating KEX_ECDH_INIT. Its live branch slices payload bytes 5..37 after the helper validator previously checked only message type, ignoring the four-byte SSH string length. Thus a type30 payload with 32 body bytes but declared length0/31/33/high-bit-set was admitted to that slice by source control flow. Non-live ssh_parse_kex_ecdh_init returned any successfully parsed string without verifying key width or full consumption. No actual executable exploit is claimed.

This is distinct from the canonical historical simpleos_ssh_qemu_gate_uses_probe_service_not_sshd_2026-06-06 KEXINIT construction failure. That record and the prior X25519 invalid-array-handle failure are not closed here.

## Contract and repair

RFC8731 section3 mandates rejecting an incorrect public-key length (32 for curve25519,56 for curve448). This server only negotiates curve25519. RFC5656 section4 defines INIT as byte message type plus string Q_C; RFC4251 section5 defines string as uint32 length plus bytes. Exactly37 payload bytes is derived from that grammar. Rejecting trailing bytes is this parser's strict whole-message policy, not a separately quoted RFC8731 MUST.

- https://www.rfc-editor.org/rfc/rfc8731#section-3
- https://www.rfc-editor.org/rfc/rfc5656#section-4
- https://www.rfc-editor.org/rfc/rfc4251#section-5

The live helper now requires length37 and encoded prefix00000020 after preserving the existing message-type/strict-kex checks. This occurs before the live slice and key/hash use. The general public parser now requires the parsed point length32 and next_offset equal to the payload length. Both return existing Err variants; session handling already disconnects and returns false. No arithmetic, algorithm advertisement, provider selection or transport framing is replaced. The existing validator is explicitly exported for direct owner testing.

## Spec-first evidence and limits

Six examples were authored before changing source: exact binary positive; every truncation0..36; inconsistent prefixes including high-bit length bytes; complete wrong-width strings0/1/31/33/56; trailing data; wrong message types including Ignore/Debug in both strict modes. Assertions call both real parser and real validator. Test: test/01_unit/os/apps/sshd/ssh_kex_ecdh_init_framing_spec.spl.

No admitted self-hosted runtime is available. All Simple execution, parser RED/GREEN, integration disconnect behavior and native byte-access correctness remain UNRUN. No seed/bootstrap fallback or shadow parser was used. Static checks are not runtime qualification. Astra source-only review is required before landing; canonical status remains OPEN until actual owner tests and session-level rejection are measured.
