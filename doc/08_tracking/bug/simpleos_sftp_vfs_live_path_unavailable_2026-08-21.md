# SimpleOS SFTP VFS live path unavailable

Status: open

`src/os/apps/sshd/ssh_sftp_v3.spl:1` advertises only SFTP v3 negotiation and
returns `SSH_FX_OP_UNSUPPORTED` for filesystem operations. The session/channel
owner is authenticated and bounded, but no VFS capability is injected, so a
real OpenSSH `sftp` client cannot list, stat, open, read, or close a SimpleOS
filesystem file.

Unblock by defining a least-authority, root-confined VFS capability owned by
the authenticated SSH session; implement bounded REALPATH/STAT/OPEN/READ/CLOSE
without host-I/O fallback; then retain a fresh QEMU transcript from OpenSSH
public-key login through SFTP v3 negotiation, one filesystem read, traversal
rejection, handle close, and session teardown.
