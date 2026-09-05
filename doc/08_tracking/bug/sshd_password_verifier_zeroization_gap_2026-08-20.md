# SSHD password verifier zeroization gap

Status: Open, production password authentication fail-closed.

`src/os/apps/sshd` has no compiler-resistant pure-Simple wipe primitive proven
for password and KDF temporary buffers. The existing byte-list wipe helpers are
crypto-module-local and are not admitted as a general credential contract.
PBKDF2-HMAC-SHA256 is available in `src/lib/common/crypto/pbkdf2.spl`, but using
it for SSH password verification before a proven wipe would retain password,
salt, HMAC, and derived-key temporaries in an unbounded compiler-visible form.

Until a compiler-resistant wipe primitive and an SSH-specific verifier record
KAT are admitted, SSHD password authentication must return false. Public-key
authentication is unaffected. Do not restore plaintext password fields or
default credentials as a workaround.
