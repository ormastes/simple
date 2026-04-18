# TLS Baremetal Verify Remaining — 2026-04-18

## Scope

Last substantive failing lane:

- `test/system/os_tls_system_spec.spl`

Hosted TLS interop and desktop integration are already green.

## Current Reality

There are two observed frontiers, and they must not be mixed:

1. A later debug lane previously reached `CertificateVerify`.
2. The exact freestanding system-test artifact still fails earlier.

The exact artifact was rebuilt with:

```sh
src/compiler_rust/target/debug/simple native-build --clean \
  --source src --source examples \
  --backend cranelift \
  --entry-closure \
  --entry examples/simple_os/arch/x86_64/tls_system_test_entry.spl \
  --target x86_64-unknown-none \
  -o build/os/simpleos_tls_system_x86_64.elf \
  --linker-script examples/simple_os/arch/x86_64/linker.ld
```

That exact ELF still fails in live QEMU at:

- `handshake failed: authentication tag mismatch`

It does not reach `Certificate`, `CertificateVerify`, or `[TLS HANDSHAKE COMPLETE]`.

## Proven On Exact Artifact

- TCP connect succeeds
- `ClientHello` is sent
- `ServerHello` is received and parsed
- X25519 shared secret path executes
- transcript/key-schedule debug markers reach the first encrypted handshake record
- first encrypted server record still fails decrypt/authentication

## Remaining Work Order

1. Restore the later decrypt/handshake-walk behavior on the exact freestanding artifact:
   - `build/os/simpleos_tls_system_x86_64.elf`
2. Reconfirm the first encrypted server handshake record decrypts and is walked on that exact artifact.
3. Only after that, continue the `CertificateVerify` Ed25519 verifier lane.

## Agent Split

### Archimedes

Owner:
- exact-artifact key schedule / traffic secret checkpoints

Files:
- `src/os/tls13/tls13.spl`
- `doc/08_tracking/bug/bug_report_tls_baremetal_u8_array_corruption_2026-04-17.md`

### Zeno

Owner:
- exact-artifact encrypted record decrypt boundary

Files:
- `src/os/tls13/record13.spl`
- `src/os/crypto/aes128_gcm.spl`
- `src/os/tls13/tls13.spl`

### Halley

Owner:
- freestanding artifact / build-shape correctness

Files:
- `examples/simple_os/arch/x86_64/tls_system_test_entry.spl`
- `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`
- `examples/simple_os/arch/x86_64/boot/curve25519_ring_helper.c`

### Copernicus

Owner:
- repro discipline and closure

Files:
- `test/system/os_tls_system_spec.spl`
- `test/system/os_tls_hosted_interop_basic_spec.spl`
- `test/system/os_tls_hosted_interop_mtls_spec.spl`

## Immediate Next Step

Use the exact freestanding artifact only, and re-narrow the failure from:

- `authentication tag mismatch`

to one of:

- wrong traffic secret
- wrong record nonce/AAD/ciphertext assembly
- AEAD/runtime corruption on the exact freestanding path
