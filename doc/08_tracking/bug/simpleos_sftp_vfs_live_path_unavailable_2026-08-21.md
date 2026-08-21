# SimpleOS SFTP VFS live path unavailable

Status: open

`src/os/apps/sshd/ssh_sftp_v3.spl` negotiates SFTP v3 and enforces bounded
framing, but every filesystem operation fails closed with
`SSH_FX_OP_UNSUPPORTED`. Implementation blockers before live use are:
`OpenFlags`/`MountTable.open` has no atomic no-follow/beneath primitive, and the
`Filesystem.readdir` contract returns a fully materialized array rather than a
bounded page/cursor. A stat-then-open check and slicing that array are rejected
as unsafe substitutes.

Unblock by adding backend-enforced no-follow/beneath open plus cursor-based
bounded readdir through the fs-driver, MountTable, and VFS layers, together
with per-principal revocable capability binding in SFTP. Then deploy an admitted Stage 4
runtime and retain a fresh QEMU transcript from OpenSSH
public-key login through SFTP v3 negotiation, one filesystem read, traversal
rejection, handle close, and session teardown.
