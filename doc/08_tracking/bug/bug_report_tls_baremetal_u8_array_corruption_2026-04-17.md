# Bug Report: Baremetal TLS encrypted-handshake record is still truncated on x86_64 after CCS

**ID:** `tls_baremetal_004`  
**Severity:** P1  
**Status:** open  
**Discovered:** 2026-04-17  
**Area:** x86_64 baremetal runtime / Cranelift compiled array layout / TLS encrypted record recv/decrypt boundary

## Summary

The remaining `test/system/os_tls_system_spec.spl` failure is no longer in transport, `ServerHello` framing, or X25519. The guest now:

- initializes VirtIO-net
- completes TCP connect to `10.0.2.2:4433`
- sends a plausible `ClientHello`
- receives and parses the first `ServerHello` record
- extracts the server key share and computes a `32`-byte shared secret

The host rustls fixture still closes with:

```text
[SERVER FAIL: unexpected end of file]
```

The newest serial trace shows the post-DH key schedule now succeeds, and the failure has moved to the first encrypted handshake record after the plaintext CCS:

```text
[tls13] after parse_server_hello cipher=4865 key_len=32
[tls13] after x25519 shared_len=32
[tls13] after server_hs_tk key_len=16 iv_len=12
[tls13] after client_hs_tk key_len=16 iv_len=12
[tls13] _io_recv_record header type=20 pay_len=<object>
[tls13] _io_recv_record header type=23 pay_len=420
[TLS FAIL: handshake failed: record too short: payload truncated]
```

That means the remaining corruption is no longer in HKDF. The guest now reaches the first encrypted handshake record, but the record presented to `record13_decrypt(...)` is still malformed or length-corrupted on the baremetal fd-mode path.

## Reproduction

```bash
bin/simple test test/system/os_tls_system_spec.spl
```

Manual repro:

```bash
src/compiler_rust/target/debug/simple native-build \
  --clean \
  --source src --source examples \
  --backend cranelift \
  --entry-closure \
  --entry examples/simple_os/arch/x86_64/tls_system_test_entry.spl \
  --target x86_64-unknown-none \
  -o build/os/simpleos_tls_system_x86_64.elf \
  --linker-script examples/simple_os/arch/x86_64/linker.ld

tools/tls_test_server/target/debug/tls_test_server \
  --config tools/tls_test_server/server.sdn

qemu-system-x86_64 \
  -machine q35 -cpu qemu64 -m 2G \
  -kernel build/os/simpleos_tls_system_x86_64.elf \
  -display none -monitor none \
  -serial file:build/os/tls_system_manual_serial.log \
  -vga std \
  -device isa-debug-exit,iobase=0xf4,iosize=0x04 \
  -netdev user,id=net0,hostfwd=tcp::14433-:4433 \
  -device virtio-net-pci,netdev=net0
```

## Expected

- Guest should derive the TLS 1.3 handshake secret and traffic secrets after X25519.
- Guest should accept the plaintext CCS and then decrypt the first encrypted handshake record.
- Host rustls fixture should continue past `ServerHello`.
- Guest should reach `[TLS HANDSHAKE COMPLETE]`.

## Actual

- Guest completes TCP, `ServerHello`, X25519, handshake-secret derivation, and handshake traffic key/IV derivation.
- The guest receives the plaintext CCS and then the first encrypted handshake record (`type=23 pay_len=420`).
- `record13_decrypt(...)` still fails with `record too short: payload truncated`.

## Technical Notes

### What is already ruled out

- VirtIO-net init and TX submission
- ARP and gateway MAC learning
- TCP active open / SYN-SYN+ACK-ACK
- direct socket send/recv return-value encoding
- `ClientHello` truncation on the send path
- first TLS record header parse on the recv path
- `ServerHello` envelope parse (`type=2`, `body_len=118`)
- X25519 shared-secret derivation itself (`shared_len=32`)
- handshake secret / handshake traffic secret derivation
- handshake traffic key/IV derivation

### Strongest current diagnosis

The remaining corruption is now in the fd-mode encrypted-record boundary after CCS. The strongest surviving suspects are:

1. small-array corruption in the fd recv path around the 1-byte CCS record
2. record assembly / length preservation bug between `_io_recv_record(...)` and `record13_decrypt(...)`
3. remaining direct-index or boxed-byte ABI problems on C-originated arrays in the record layer

### Files involved

- `src/os/tls13/tls13.spl`
- `src/os/tls13/record13.spl`
- `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`
- `examples/simple_os/arch/x86_64/tls_system_test_entry.spl`
- `test/system/os_tls_system_spec.spl`

## Recommended Next Steps

1. Instrument `_io_recv_record(...)` and `record13_decrypt(...)` with explicit `raw_record.len()` and header-byte dumps on the first `type=23` record.
2. Inspect the fd recv bridge for small-array anomalies, especially the 1-byte CCS path that still logs as `pay_len=<object>`.
3. If needed, bypass the generic record-layer parse for fd-mode by copying the raw record into a known-good C-owned or Simple-owned buffer before decrypt.
