# SSH X25519 shared-secret rejection

Executable: test/01_unit/os/apps/sshd/ssh_x25519_shared_secret_rejection_spec.spl

Status: manual companion, seven examples authored, runtime UNRUN. No generated or measured PASS.

1. Reject exactly 32 zero bytes.
2. Reject empty, 31-byte and 33-byte outputs including nonzero values.
3. Accept each of 32 nonzero positions with values 01/7f/80/ff (128 cases).
4. Reject private/peer lengths 0/31/33 before provider calls (six cases).
5. Reject real-provider low-order peers zero and one, including their high-bit aliases (four cases).
6. Preserve both published RFC7748 section 6.1 exchange directions.
7. Preserve the published result with the peer high bit set.

Oracle: https://www.rfc-editor.org/rfc/rfc7748#section-6.1 . SSH rejection requirement: https://www.rfc-editor.org/rfc/rfc8731#section-3 .

Server use is wired after the selected provider and before exchange-hash computation. Its actual disconnect behavior and compiled timing properties are not verified by this unexecuted unit specification.
