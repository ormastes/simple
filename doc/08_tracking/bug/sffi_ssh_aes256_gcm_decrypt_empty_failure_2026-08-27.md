# SSH AES-256-GCM SFFI decrypt collapses failure into an empty byte array

- Status: OPEN
- Filed: 2026-08-27
- Severity: security boundary / cross-lane SFFI contract defect
- Scope: `rt_ssh_aes256_gcm_decrypt_packet`

## Evidence

The raw Simple declaration in
`src/os/apps/sshd/ssh_cipher_live.spl` returns `[u8]`, which has no failure
state.  The native Rust provider in
`src/compiler_rust/runtime/src/value/aes.rs` converts every invalid input or
authentication failure from `ssh_aes256_gcm_decrypt_packet_bytes` to
`empty_runtime_array()`.  The Rust interpreter handler in
`src/compiler_rust/compiler/src/interpreter_extern/simd.rs` independently does
the same with `unwrap_or_default()`.

The Simple wrapper currently interprets an empty result as
`Err("GCM packet decryption failed")`.  This is not a typed raw contract, and
it still represents a foreign failure as a fabricated ordinary value before
the wrapper happens to inspect it.  It also leaves native and interpreter
implementations independently responsible for retaining identical sentinel
semantics.

`rt_ssh_aes256_gcm_decrypt_packet_payload_len` returns `-1` on the same
failure class, but calling it before the payload function would decrypt and
authenticate the packet twice.  That is not an acceptable safety repair
because it adds avoidable crypto work and allocation pressure to the SSH hot
path.

## Required resolution

Introduce one canonical, single-pass v2 raw contract.  It must return an
explicit status plus an output descriptor (or an equally explicit tagged
descriptor), with these semantics:

```text
OK                 -> initialized authenticated payload
AUTH_FAILED        -> no payload
INVALID_ARGUMENT   -> no payload
INTERNAL_FAILURE   -> no payload
```

Generate or implement one lifting wrapper returning
`Result<[u8], SshCryptoError>` and make the old v1 raw entry unsafe-only during
migration.  Update all of the following from the same contract definition:

- Rust native provider/export;
- Rust interpreter extern registration/handler;
- JIT/native registration and dynload ABI metadata;
- Simple SSH safe wrapper and its raw declaration;
- negative conformance fixtures for malformed input and tampered tag.

The v2 implementation MUST decrypt/authenticate once per call, retain cached
typed dispatch, and add neither per-call hashing/signature lookup nor a second
payload copy beyond the already-required owned Simple result.  It MUST NOT use
empty arrays, `0`, `false`, or `nil` as failure sentinels.

## Acceptance evidence

1. Native, interpreter, JIT/AOT, and sealed-dynload lanes yield the same typed
   error category for malformed key/IV/packet and tag mismatch.
2. A valid encrypted packet yields its exact payload, including the documented
   empty-payload policy if SSH packet rules ever admit it.
3. The v1 symbol cannot be called from safe Simple code.
4. A focused benchmark demonstrates one AES-GCM decrypt/authentication per
   successful or failing wrapper call, with no new per-call lookup, hash, or
   auxiliary allocation.
5. The provider remains unsigned/unverified until its exact artifact, ABI
   registry, and evidence manifest are admitted by the SFFI v2 loader policy.
