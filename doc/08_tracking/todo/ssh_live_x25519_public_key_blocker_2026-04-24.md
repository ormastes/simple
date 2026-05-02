# SSH Live X25519 Public-Key Blocker — 2026-04-24

## Summary

The original live-lane blocker in this note is fixed. The remaining defect is
now narrower and later in the SSH handshake: OpenSSH still aborts after
`SSH_MSG_KEX_ECDH_REPLY`, but the guest now produces valid 32-byte X25519
values, a full 32-byte exchange hash, and a standard-valid Ed25519 signature
over the guest-computed exchange hash.

## Symptom

Fresh live kernel boot now reaches host-key signing, sends
`SSH_MSG_KEX_ECDH_REPLY`, and OpenSSH aborts with:

```text
ssh_dispatch_run_fatal: Connection to 127.0.0.1 port 2299: incorrect signature
```

Current live serial evidence on the Cranelift x64 guest:

- `server ecdh priv len=32 pub len=32`
- `shared secret len=32`
- `exchange hash len=32`
- `sig self-verify rc=1 pub len=32 raw len=64`

The emitted Ed25519 signature also verifies off-guest with OpenSSL against the
guest-logged public key and exchange hash, so the remaining mismatch is in the
SSH exchange-hash inputs seen by OpenSSH rather than in Ed25519 signing itself.

## Reproduction

```bash
bin/simple test test/system/ssh_live_login_in_qemu_spec.spl
```

The system spec now proves this is a fresh kernel by checking the guest serial
for the current `[boot] Build marker: ...` line.

## Impact

- Blocks password-authenticated OpenSSH login in the `x64-ssh` QEMU lane
- Prevents `simpleos_guest_toolchain_live_spec` from moving past SSH login
- Leaves the runtime/X25519/SHA/Ed25519 primitive fixes in place, but the live
  guest still disagrees with OpenSSH on the KEX exchange hash inputs

## Current Status

- Fresh-artifact build gate: fixed
- Live guest reaches real KEX path: fixed
- Baremetal runtime X25519 helper path (`rt_tls13_x25519_*`) now returns stable 32-byte arrays for both fixed and random scalars in the native-built x64 guest probe.
- Baremetal SHA-256 truncation in the live lane: fixed via runtime fallback path
- Baremetal Ed25519 host-key signing path now uses direct runtime return-value helpers and produces signatures that verify both in-guest and off-guest.
- The remaining live-lane blocker has moved past KEX public-key generation and past host-key signing itself: OpenSSH still aborts with `incorrect signature` after the guest sends `SSH_MSG_KEX_ECDH_REPLY`.
- Server X25519 public key derivation in baremetal guest: fixed for the runtime helper path used by the live SSH lane
- Next blocker: post-KEX exchange-hash input mismatch between the guest and OpenSSH
