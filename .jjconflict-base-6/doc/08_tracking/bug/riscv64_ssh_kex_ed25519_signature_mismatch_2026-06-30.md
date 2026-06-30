# RV64 SSH KEX Ed25519 Signature Mismatch

Date: 2026-06-30

## Status

Open. Narrowed to RV64 freestanding X25519 shared-secret generation.

## Summary

The RV64 QEMU SSH-live scenario now reaches OpenSSH key exchange, sends the SSH
banner, sends server KEXINIT, receives client KEXINIT and KEX_ECDH_INIT, then
sends `SSH2_MSG_KEX_ECDH_REPLY` and `NEWKEYS`. OpenSSH rejects the server
Ed25519 signature in the ECDH reply.

## Evidence

Scenario command:

```sh
timeout 420s bin/simple os test --scenario=rv64-ssh
```

Log:

```text
build/os/rv64_ssh_scenario_probe_live_kex_direct_20260630.log
```

Important markers:

```text
[sshd] accepted client fd=200
[sshd-session] version direct banner send rc=22
[sshd-session] live plain kexinit rc=200
[sshd-session] client ecdh pub len=32
[sshd-session] server public generation len=32
[sshd-session] shared secret generation len=32
[sshd-session] exchange hash len=32
[sshd-session] host ed25519 sign pure len=64
[sshd-session] live plain kex reply rc=192
[sshd-session] live plain newkeys rc=16
debug1: SSH2_MSG_KEX_ECDH_REPLY received
debug2: ssh_ed25519_verify: crypto_sign_ed25519_open failed: -1
```

Follow-up evidence after preserving fd `200` and simplifying the live KEX path:

```text
build/os/rv64_ssh_scenario_probe_x25519_shared_markers_20260630.log
```

Important markers:

```text
X25519 SHARED ENTER
X25519 SHARED COPIED
X25519 SHARED ECHO
[sshd-session] exchash sha qc=66687aadf862bd776c8fc18b8e9f8e20089714856ee233b3902a591d0d5f2925
[sshd-session] exchash sha k=66687aadf862bd776c8fc18b8e9f8e20089714856ee233b3902a591d0d5f2925
debug2: ssh_ed25519_verify: crypto_sign_ed25519_open failed: -1
```

The Ed25519 signature logged by the server verifies locally against the logged
exchange hash and the advertised RFC 8032 host key, so the signing primitive and
host-key blob are not the immediate failure. OpenSSH rejects the signature
because it computes a different exchange hash: the RV64 freestanding X25519
helper returns the peer public key as the shared secret (`K == Q_C`). The RV64
helper now clamps the raw scalar before calling ring's
`x25519_scalar_mult_generic_masked`, matching the x86 helper, but QEMU still
reports `X25519 SHARED ECHO`.

Next fix: repair or replace the RV64 freestanding `rt_tls13_x25519_shared_secret`
implementation in `examples/09_embedded/simple_os/arch/riscv64/boot/curve25519_ring_helper.c`
so it matches RFC 7748 on QEMU, then rerun `bin/simple os test --scenario=rv64-ssh`.
