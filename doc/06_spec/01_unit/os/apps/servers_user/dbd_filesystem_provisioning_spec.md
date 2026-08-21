# Filesystem-launched DBD provisioning

The operator boots the combined HTTP/database payload from its verified
filesystem image. Before either database listener or recovery begins, the
payload reads the credential, certificate chain, and PKCS#8 private key into
bounded mutable buffers. It calls the canonical `DbdServer.provision_service`
once and immediately zeroes all three source buffers with verified readback.

The payload consumes the typed
`DbfsMountedRecoveryCompleteDurableTransactionalReplace` state through
read-only syscall 79. The capability vocabulary has one shared common OS
contract type; VFS alone encodes its published state and userlib alone decodes
the syscall result. VFS clears it before each root mount and publishes it
only after a device-backed DBFS driver mounts with live durability
serialization. Missing that state stops startup. A successful admission recovers
the canonical checksummed journal, authenticates the client inside TLS, commits
each mutation through the DBFS adapter before replying, and serves later reads
from the same canonical DBD owner. No credential is accepted in argv, source,
or an immutable text conversion.

Operator-visible failures name the first boundary: boot material, DBFS/VFS
capability, recovery, or listener startup. They never print secret bytes.

Each replacement uses an exclusive generation-owned staging path, syncs its
contents, performs the transactional DBFS rename, and syncs the root namespace
before acknowledgement. Every post-provisioning exit invokes whole-owner close
to wipe retained certificate, private-key, and verifier material.
