# SSH accepts a 32-byte all-zero X25519 result

Status: OPEN — source repair proposed; runtime verification pending.

RFC 8731 section 3 requires rejection of an all-zero computed X25519 shared secret and incorrect peer-public-key lengths: https://www.rfc-editor.org/rfc/rfc8731.html#section-3 . This is an SSH admission rule, not an arithmetic replacement.

## Source evidence

The pure-Simple path is ssh_kex_core.spl -> os.crypto.curve25519.x25519 -> curve25519_smalllimb.x25519_smalllimb. It computes/serializes the field result without a protocol-level all-zero rejection. ssh_kex_compute_shared accepted any length-32 output; duplicate ssh_kex_crypto did likewise. ssh_client_kex.spl checks only returned length before hashing/deriving keys. The server ssh_session_kex.spl calls either the pure function or its configured alpha provider, then checked length alone before hashing/derivation. A separate Rust ring SFFI provider rejecting low-order peers cannot guarantee this pure branch. This is source evidence of missing validation, not a newly executed exploit.

## Repair

ssh_x25519_shared_secret_valid rejects lengths other than 32 and reduces all 32 bytes with OR before checking nonzero. Both shared-secret wrappers return their existing empty error result for invalid key lengths or rejected outputs. Client handling already converts empty to Err. The direct server path validates the selected provider result and disconnects with SSH_DISCONNECT_KEY_EXCHANGE_FAILED before further use. Provider selection, byte order, clamp rules and arithmetic remain unchanged. The byte scan has no secret-dependent early return; compiled constant-time behavior is not claimed.

## Verification boundary

Seven new SSpec examples cover all-zero, malformed output/key lengths, each nonzero byte position with 01/7f/80/ff, low-order zero/one peers and high-bit aliases, and independent RFC7748 section 6.1 shared-secret vectors in both directions. Expected published bytes are literal in the spec. These are authored regressions, not executed results. No approved self-hosted runtime is available; compiler/bootstrap is excluded by campaign instructions. Runtime, low-order provider behavior and server disconnect execution remain UNRUN.

The separate retained native invalid-array-handle failure in curve25519_local_byte_helper_name_2026_10_27.md remains open and is not repaired or qualified by this guard. No algorithm/provider substitution, seed execution or network security assurance is claimed.

Focused command once an admitted runner exists:
`<admitted-runtime> test test/01_unit/os/apps/sshd/ssh_x25519_shared_secret_rejection_spec.spl`
Then exercise server disconnect for rejected results on its configured live provider; inspect response and ensure no exchange hash/key derivation proceeds. Source admission requires Astra review; this record is not production verification PASS or canonical closure.
