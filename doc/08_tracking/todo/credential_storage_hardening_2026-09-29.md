# Harden saved credentials across Windows, Linux, macOS and BSD

Status: OPEN. Priority: high. Requested by user on 2026-09-29.
Owner: stdlib security / host credential provider.

Current implementation: `src/lib/nogc_sync_mut/terminal/credential/store.spl`.
The v2 record uses AES-256-CBC with a random IV, but has no authentication tag.
The final decryption key is saved in `~/.simple/credential_key` as encoded key
bytes, protected by file permissions rather than a separate wrapping key.
Encryption therefore does not protect against theft of both config and key.
The module documentation also incorrectly describes the current hex key-file
format as base64. No cross-platform security claim follows from mode 0600.

The user accepts reusing this format for mail now, with these limitations
documented. This TODO does not certify the existing store as hardened.

Required follow-up:

1. Introduce one host credential interface with native providers: Windows
   Credential Manager/DPAPI, macOS Keychain, and Secret Service on supported
   Linux/BSD installations. Keep platform dispatch out of app code.
2. Protect the encryption key through those providers. Define a headless
   encrypted-vault option with an independently supplied unlock secret; do not
   store the unlock secret alongside the ciphertext. Fail closed if unavailable.
3. Introduce a versioned authenticated-encryption format using a reviewed AEAD
   implementation, binding account/server/protocol identity as associated data.
   Reject tampering and truncation before returning plaintext; do not invent a
   cipher, MAC, nonce scheme, or password KDF.
4. Migrate legacy records explicitly and atomically, retaining recovery until
   read-back succeeds. Never overwrite an existing key or silently downgrade.
5. Verify Windows ACLs and POSIX permissions, parent directories, symlink
   handling, atomic replacement, concurrent updates, key rotation and backup.
6. Minimize plaintext lifetime and prevent argv/log/error/trace disclosure.

Acceptance: independent review plus native Windows/macOS/Linux/FreeBSD tests;
headless locked/unavailable-store cases; wrong-key, modified-IV/ciphertext/tag,
truncation, cross-account substitution, migration interruption, rotation and
permission checks. Other BSDs require their own evidence, not FreeBSD inference.
