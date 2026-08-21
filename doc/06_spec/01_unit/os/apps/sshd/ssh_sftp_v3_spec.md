# SSH SFTP v3 Protocol Core

Source: `test/01_unit/os/apps/sshd/ssh_sftp_v3_spec.spl`

Evidence class: `host-fixture`.

## Scenarios

- Negotiate exactly SFTP v3 and reject requests before initialization, path
  traversal, malformed frames, and oversized packets.
- Reassemble split headers and byte-fragmented frames while retaining a
  coalesced following frame.
- Reject every filesystem request after negotiation until a per-principal,
  revocable VFS namespace capability provides atomic beneath/no-follow lookup
  and bounded paged iteration.
- Route every SSH terminal transition through the cleanup owner.
- Recognize only the exact SSH `sftp` subsystem request and reject trailing
  bytes.

The fixture proves bounded protocol/VFS semantics, not a live network session.
