# SSH Live X25519 Public-Key Blocker — 2026-04-24

## Summary

After the live build lane was hardened to require a fresh
`build/os/simpleos_ssh_live_32.elf`, the QEMU login spec advanced to the real
runtime KEX failure inside the guest.

The remaining blocker is server ephemeral key generation for the live SSH lane:
`ssh_kex_public_from_private` does not currently yield a valid 32-byte `Q_S`
for the baremetal guest.

## Symptom

Fresh live kernel boot succeeds and reaches SSH KEX, then the guest disconnects:

```text
[sshd-session] client ecdh pub len=32
[sshd-session] disconnect reason=5236088 description=server X25519 public failed
```

Two attempted implementations were observed during this pass:

- pure `x25519_base(private)` in the guest:
  allocates until `[PANIC] heap exhausted`
- handle-based hosted DH FFI:
  not usable in the baremetal guest path, returning no valid 32-byte public key

## Reproduction

```bash
bin/simple test test/system/ssh_live_login_in_qemu_spec.spl
```

The system spec now proves this is a fresh kernel by checking the guest serial
for the current `[boot] Build marker: ...` line.

## Impact

- Blocks the live `curve25519-sha256` reply path before `Q_S`, `H`, and the
  Ed25519 signature can be fully validated against OpenSSH
- Prevents password-authenticated OpenSSH login in the `x64-ssh` QEMU lane
- Leaves the hosted transcript/signature regressions green, but the live guest
  still fails before authentication

## Current Status

- Fresh-artifact build gate: fixed
- Live guest reaches real KEX path: fixed
- Server X25519 public key derivation in baremetal guest: blocked
