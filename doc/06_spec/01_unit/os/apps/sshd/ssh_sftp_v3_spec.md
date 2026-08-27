# SSH SFTP v3 Protocol Core

Source: `test/01_unit/os/apps/sshd/ssh_sftp_v3_spec.spl`

Evidence class: `host-fixture`.

## Scenarios

- Negotiate exactly SFTP v3 and reject requests before initialization, path
  traversal, malformed frames, and oversized packets.
- Reassemble split headers and byte-fragmented frames while retaining a
  coalesced following frame.
- Round-trip OPEN, WRITE, READ, STAT, and CLOSE through canonical DBFS VFS
  objects; reject non-atomic append and stale or retired objects.
- Route every SSH terminal transition through the cleanup owner.
- Recognize only the exact SSH `sftp` subsystem request and reject trailing
  bytes.

The fixture proves bounded protocol/VFS semantics, not a live network session.

