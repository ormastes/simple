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

---

## Lane disposition 2026-11-13 (live-p3-l4, work/live-p3-l4-20261113, base f790f7f266e)

Re-checked at this base: unchanged — `src/os/apps/sshd/ssh_sftp_v3.spl` still advertises SFTP v3 negotiation only and returns `SSH_FX_OP_UNSUPPORTED` for filesystem operations; no VFS capability is injected into the authenticated session. The unblock condition (least-authority root-confined VFS capability owned by the SSH session; bounded REALPATH/STAT/OPEN/READ/CLOSE without host-I/O fallback; retained QEMU transcript from OpenSSH public-key login through SFTP read/traversal-rejection/close/teardown) is a feature with a live-hardware evidence requirement — not a P3 bug-box fix, and this lane has no SimpleOS QEMU target. No in-lane change. Owner: SimpleOS sshd/VFS lane.
