# Secure SSH and hybrid-PQC interoperability

**Status:** PARTIAL/RED — the executable negotiation-boundary scenario proves
required hybrid mode refuses classical selection, refuses advertising the
hybrid name while wire crypto is unavailable, and forbids classical retry after
hybrid failure. Live Simple SSH/OpenSSH negotiation, authentication, exec,
transfer, and hybrid wire-KEX oracles remain unresolved.

The unresolved bidirectional matrix is required to cover Simple client ->
SimpleOS sshd, Simple client -> OpenSSH, and OpenSSH -> SimpleOS sshd. It must
pin host-key, AEAD, classical and X25519+ML-KEM-768 KEX profiles; verify
transcript binding and known-host policy; and reject downgrade, replay,
malformed KEX, authentication failure, and selected-hybrid failure without an
insecure retry. The current executable evidence covers only the fail-closed
hybrid negotiation-policy boundary described above.

**Executable SPipe:** `test/03_system/network/ssh/secure_ssh_pqc_interop_spec.spl`
