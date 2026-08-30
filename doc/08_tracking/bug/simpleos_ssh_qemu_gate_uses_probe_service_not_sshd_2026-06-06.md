# SimpleOS SSH QEMU Gate Production SSHD Live Proof

Status: Fix implemented — awaiting live OpenSSH/QEMU verification.

Date: 2026-06-06

## Status

Fix implemented — awaiting live OpenSSH/QEMU verification.

## Summary

The live SSH QEMU gate now starts the production `SshDaemon` from
`examples/09_embedded/simple_os/arch/x86_64/ssh_live_entry.spl` instead of the old
line-oriented TCP probe. Host-side OpenSSH reaches the guest and the daemon accepts
connections on port 22, but the live handshake still fails before key exchange completes.

The remaining blocker is pure Simple/baremetal packet construction: the server KEXINIT
payload emitted on the wire is corrupt in the live lane. Current serial evidence shows
`payload_len_raw=62` and the packet payload starts with `0x54` instead of SSH message
`0x14`, after which OpenSSH closes and the daemon reports `bad KEXINIT` or
`no KEXINIT received`.

## 2026-08-22 Fix

`SshSession.send_packet` now uses the canonical Pure-Simple
`ssh_packet_build(payload, send_seq)` path for every plaintext packet, including
KEXINIT, ECDH reply, and NEWKEYS. The old `fd == 200` message-specific path sent
an unframed SPL payload across a second runtime framing boundary; that is the
boundary which observed `0x54` in place of payload byte zero `0x14`.

The replacement performs one bounded O(payload bytes) packet construction and
one send, removes three live-only dispatch branches, and preserves the public
session and transport APIs. Focused coverage checks the complete production
KEXINIT through canonical packet parse/round-trip and verifies that the QEMU
target starts `SshDaemon` while the host oracle drives OpenSSH authentication.
Live QEMU evidence is still required before this report can be closed.

## Evidence

- `examples/09_embedded/simple_os/arch/x86_64/ssh_live_entry.spl` starts `SshDaemon`.
- `src/os/ssh_qemu_contract.spl` launches QEMU and then drives host OpenSSH against
  `127.0.0.1:2222`.
- Latest failing live run:
  - `bin/release/x86_64-unknown-linux-gnu/simple test test/03_system/os/ssh_live_login_in_qemu_spec.spl --mode=interpreter --json --timeout 900 --clean`
  - JSON: `/tmp/ssh_live_qemu_production_guard_restored.json`
  - Serial: `build/os/x64-ssh-live.serial.log`
- Passing non-live production transcript:
  - `test/02_integration/os/apps/sshd/sshd_production_packet_transcript_spec.spl`: 1 passed, 0 failed.
- Passing daemon unit smoke:
  - `test/01_unit/os/apps/sshd/sshd_spec.spl`: 6 passed, 0 failed.

## Required Fix

Fix the pure Simple/baremetal KEXINIT construction path so the first server packet after
version exchange is a valid plaintext SSH packet:

1. packet length/padding are valid
2. payload byte 0 is `SSH_MSG_KEXINIT` (`0x14`)
3. advertised host-key algorithms match staged live keys
4. OpenSSH proceeds to ECDH init
5. the gate reaches password auth success and bad-password fail-closed markers

## Notes

Ed25519 is intentionally disabled in the live RSA lane pending a separate baremetal KAT fix.
