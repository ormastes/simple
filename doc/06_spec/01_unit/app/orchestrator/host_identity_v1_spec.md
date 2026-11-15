# Public identity, immutable pin and private codec contracts

Source: [host_identity_v1_spec.spl](../../../../../test/01_unit/app/orchestrator/host_identity_v1_spec.spl).
Manually authored companion; **NOT_RUN**. The source uses published RFC 8032
fixture material. It contains no execution receipt for a generated operational
key, store publication, registration, or OpenSSH interoperability run.

## Manual flow represented by the assertions

1. Parse one Ed25519 public key and derive its OpenSSH SHA-256 wire fingerprint.
   Remove its comment and accept one terminal CRLF without changing identity.
2. Compare a server key against an independently supplied expected fingerprint
   before the first pin. Accept the same key with another comment; reject a
   changed key even when its new fingerprint is supplied.
3. Export a registration request from canonical public material. Check the
   explicit `registration-request-exported`, grant-required and possession
   not-performed fields. Export does not send or enroll anything. Revalidate a
   fabricated public-key struct before encoding any reply.
4. Validate command authority and options before store IO. Generation requires
   an explicit store root and valid reference. Omitted `--name` selects a bounded
   current-time public label; an explicit name preserves the existing text-hash
   label format. Explicit empty or overlong names fail instead of selecting the
   default. Public-file reads require an acceptable absolute `.pub` path.
5. Round-trip the published seed/public pair through the OpenSSH private codec.
   Reject an inconsistent embedded public key, malformed private input, invalid
   codec sizes and malformed/zero entropy input.

| Failure group | Authored rejection checks |
|---|---|
| Public material | Empty/unsupported/malformed encoding, wrong embedded wire algorithm, multiple keys, controls and private-key headers. Diagnostics must not echo private source. |
| Trust decision | Wrong expected fingerprint and changed pinned key. |
| Command admission | Omitted-name and named generation admission; invalid explicit empty/overlong names, invalid server/reference, omitted store authority, unknown/duplicate/missing/extraneous options, relative/traversing paths and private-key filename. |
| Public naming | Exact current-time and known text-hash labels, bounded maximum timestamp, failed clock sample and no empty-name fallback. Naming supplies no private entropy. |
| Private codec | Inconsistent seed/public pair, malformed private file, invalid sizes and invalid entropy spelling. |

Requirements: REQ-002/006 and NFR-002. These pure/early-rejection scenarios do
not establish entropy-provider quality, private-store durability, ACL policy,
secure erasure on a native producer, actual `ssh-keygen` acceptance or server
authorization. Retained `host_identity_store_v1` publication/cleanup and both
platform providers require their own execution evidence. See
[identity setup](../../../../07_guide/tooling/orchestration_host_identity.md),
[exchange manual](host_identity_exchange_v1_spec.md) and
[verification plan](../../../../03_plan/sys_test/server_contexts.md).

The existing-identity early return remains before the clock sample and key
generation call. This source preservation is not a runtime idempotence receipt;
store/entropy observation under an admitted producer remains NOT_RUN.

Private-envelope prevention cases reject multibyte and control-bearing suffixes with the exact format error. These authored cases are NOT_RUN; no truncation failure was experimentally reproduced.
