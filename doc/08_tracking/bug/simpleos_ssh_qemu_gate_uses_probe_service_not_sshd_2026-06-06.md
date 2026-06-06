# SimpleOS SSH QEMU Gate Uses Probe Service Instead Of Production SSHD

Date: 2026-06-06

## Status

Open.

## Summary

The current live SSH QEMU gate does not prove the production SSHD packet stack. It starts
`examples/09_embedded/simple_os/arch/x86_64/ssh_live_entry.spl`, which behaves as a TCP
banner/probe service with line-oriented commands such as `AUTH root simpleos` and
`SESSION shell ...`.

That is useful as a network reachability smoke, but it does not verify real SSH transport,
key exchange, authentication, channel handling, encryption, MAC, or host-key compatibility.

## Evidence

- `src/os/ssh_qemu_contract.spl` probes the service via shell `/dev/tcp`.
- `examples/09_embedded/simple_os/arch/x86_64/ssh_live_entry.spl` implements the probe protocol.
- Production SSHD logic lives under `src/os/apps/sshd/`, especially:
  - `ssh_transport.spl`
  - `ssh_session_kex.spl`
  - `ssh_kex.spl`
  - `host_key_loader.spl`
  - `sshd.spl`

## Required Fix

Add an integrated SSHD gate that drives the production `src/os/apps/sshd` stack through at least:

1. protocol version exchange
2. KEXINIT
3. ECDH/KEX reply with selected host key
4. NEWKEYS
5. service request
6. userauth
7. channel open/request/data/close

Then add a live OpenSSH compatibility smoke for the same production path. Keep the existing probe
service as a network smoke only, and name it accordingly so it is not mistaken for SSHD coverage.

## Notes

Avoid crypto overlap while `ed25519` and `rsa-pss` signature blockers are open. The first safe
step is an in-memory packet transcript spec that validates production session state transitions
without changing signature code.
