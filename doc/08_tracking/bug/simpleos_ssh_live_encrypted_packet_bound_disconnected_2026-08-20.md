# SimpleOS live SSH encrypted packet bound is disconnected

**Status:** IMPLEMENTED — admitted-runtime evidence remains release-blocking
**Owner:** live SSH AES-GCM receive path and canonical socket facade
**Found:** 2026-08-20

## Defect

The production `SshSession` AES-GCM receive path now calls
`ssh_encrypted_packet_frame_allowed` immediately after the socket owner returns
the frame. It rejects a body outside 2..35,000 bytes and requires exact
`4 + advertised body + 16-byte GCM tag` length before ciphertext logging,
decryption, or cipher sequence advancement. The buffered compatibility path
applies the same validator before observing or decrypting its extracted frame.
The SSH-specific socket facade now applies the same ceiling immediately after
its four-byte header read and before reading or allocating the encrypted body
and tag. Its former fd-200 whole-frame shortcut was removed, so that path also
uses the checked `rt_net_ssh_encrypted_read_plan` typed read plan. Generic socket and
non-SSH protocol limits are unchanged.

Behavioral unit coverage includes the exact frame, truncated tag, trailing byte,
short body, and maximum+1 cases. No source-text predicate is used.

The formerly duplicated 1,357-line baremetal SSH system spec is now one shared
suite with protocol and crypto profile modules (749 and 541 lines). The
`test/03_system/os/os_ssh_spec.spl` canonical entry and legacy
`test/system/os_ssh_spec.spl` compatibility entry are five-line facades over
that same scenario owner; scenario bodies are not copied.

## Required closure evidence

- Exercise the production AES-GCM receive path, not a standalone predicate,
  with an admitted self-hosted runtime and target/QEMU receipt.

## Quadratic receive accumulation removed 2026-08-21

Handed over from the TLS/SFTP accumulator lane: SSH transport was the remaining
quadratic stage feeding the now-linear SFTP layer. The buffered encrypted
receive path in `src/os/apps/sshd/ssh_session.spl` did
`recv_buf = rt_bytes_concat(recv_buf, more)` on every socket fragment (twice:
header fill and body fill) and `recv_buf = _slice_range(recv_buf, n, len)`
after every consumed frame. All three rebuild the whole buffer, so framing one
packet out of N fragments cost O(N^2) byte copies.

Fix: new fixed-capacity owner `src/os/apps/sshd/ssh_recv_ring.spl`
(`SshRecvRing`). Each admitted byte is written exactly once at
`(head + count) % cap`; consumption advances `head` and never rebuilds the
remainder. Capacity is 45,056 bytes — a maximal admissible AES-GCM frame
(4 + 35,000 + 16 = 35,020) plus one 8,192-byte socket read — and a push that
does not fit is rejected in full (no partial write, no reallocation), bounding
the memory a peer can pin; the session closes on overflow. `ssh_session.spl`'s
`recv_buf: [u8]` field is replaced by `recv_ring: SshRecvRing`; the packet
length is read in place via the new `ssh_recv_ring_u32_be` rather than
materializing a prefix. The `ssh_encrypted_packet_frame_allowed` bound is
applied unchanged to the extracted frame.

Evidence — `test/01_unit/os/apps/sshd/ssh_recv_ring_spec.spl`:

`SPEC FILE VERDICT: test/01_unit/os/apps/sshd/ssh_recv_ring_spec.spl outcome=OK declared>=15 executed=15 passed=15 failed=0 skipped=0 dropped=0`

Covers linearity (4,096 bytes fed one byte at a time performs exactly 4,096
byte writes; 4x the bytes costs 4x the work, not 16x; fragment size does not
change total work), the fragmentation cases (one byte at a time, a length split
across fragments, a coalesced two-frame read, wrap-around at the physical end),
the fail-closed bound (over-capacity push writes nothing, exact capacity then
refusal, over-take refused), and `ssh_session.spl`'s own ring-backed length
reader plus its frame validator. Regression: `ssh_session_shell_spec.spl`
`Results: 14 total, 14 passed, 0 failed`.

The closure evidence requirement above (production AES-GCM receive path on an
admitted self-hosted runtime with a target/QEMU receipt) is unchanged and still
open.

## Channel lifecycle and flow-control closure 2026-08-21

The live channel owner now applies its advertised 32 KiB packet ceiling before
decrementing the receive window. Data is rejected for unknown, closed, or
peer-EOF channels. Window adjustments must be nonzero, target an open channel,
and fit checked `u32` arithmetic. Peer EOF is recorded exactly once as a receive
half-close; it does not prematurely discard the channel. A CLOSE for an unknown
recipient fails the session closed instead of emitting a CLOSE for channel 0.

Focused behavioral coverage is in
`test/01_unit/os/apps/sshd/ssh_channel_open_capacity_spec.spl`. Runtime execution
remains pending because this isolated non-bootstrap worktree has no admitted
self-hosted `bin/release/.../simple` executable.
