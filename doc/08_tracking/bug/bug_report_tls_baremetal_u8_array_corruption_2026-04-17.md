# Bug Report: Baremetal TLS first encrypted handshake record fails authentication on x86_64 after CCS

**ID:** `tls_baremetal_004`  
**Severity:** P1  
**Status:** open  
**Discovered:** 2026-04-17  
**Area:** x86_64 baremetal runtime / TLS fd-mode key schedule / handshake traffic secret or decrypt boundary

## Summary

The remaining `test/system/os_tls_system_spec.spl` failure is no longer in transport, `ServerHello` framing, or fd-mode X25519. The guest now:

- initializes VirtIO-net
- completes TCP connect to `10.0.2.2:4433`
- sends a plausible `ClientHello`
- receives and parses the first `ServerHello` record
- extracts the server key share and computes a `32`-byte shared secret that matches an independent host-side X25519 recomputation

The host rustls fixture still closes with:

```text
[SERVER FAIL: unexpected end of file]
```

The newest serial trace shows the post-DH key schedule now succeeds, the earlier record-length truncation bug is fixed, and the failure has moved to the first encrypted handshake record after the plaintext CCS:

```text
[tls13] after parse_server_hello cipher=4865 key_len=32
[tls13] after x25519 shared_len=32
[tls13] after server_hs_tk key_len=16 iv_len=12
[tls13] after client_hs_tk key_len=16 iv_len=12
[tls13] _io_recv_record header type=20 pay_len=<object>
[tls13] _io_recv_record header type=23 pay_len=420
[record13] decrypt raw_len=425 seq=0
[record13] header b0=23 b1=3 b2=3 b3=1 b4=164
[record13] payload_length=420
[TLS FAIL: handshake failed: authentication tag mismatch]
```

That means the remaining corruption is no longer in X25519 or record-length arithmetic. The guest now reaches the first encrypted handshake record with a consistent 425-byte buffer and valid TLS header bytes, but the AEAD decrypt still fails authentication on the baremetal fd-mode path.

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
- `record13_decrypt(...)` now reaches AEAD validation and fails with `authentication tag mismatch`.

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
- record-length truncation arithmetic on the first encrypted record

### Strongest current diagnosis

The remaining corruption is now clearly above record decryption and below the `ClientHello` / `ServerHello` transcript boundary:

1. the fd-mode shared-secret helper in `curve25519_ring_helper.c` was wrong because it fed an unclamped scalar into `ring`'s `x25519_scalar_mult_generic_masked(...)`
2. clamping the scalar and masking the peer u-coordinate fixed that bug; the guest's `dhe_shared` now matches an independent host-side X25519 recomputation exactly
3. despite that, the guest's `CLIENT_HANDSHAKE_TRAFFIC_SECRET` and `SERVER_HANDSHAKE_TRAFFIC_SECRET` still do not match the server's rustls key log output
4. using the guest's logged `dhe_shared` and `transcript_sh_hash`, an external HKDF recomputation also does not reproduce the guest's `client_hs_secret` / `server_hs_secret`

That means the active remaining bug is now in the baremetal fd-mode key-schedule path, not in X25519. The strongest remaining suspects are:

1. `rt_tls13_hkdf_extract(...)` after `hs_derived`
2. the later fd-mode handshake-traffic secret expansion path after `handshake_secret`
3. only after those, any remaining divergence in transcript-hash ownership or record decrypt

Attempting to switch fd-mode back to the pure Simple key-schedule path is not usable yet: it regresses to runaway `0x1010` heap growth and eventual heap exhaustion on baremetal, so the C-backed fd-mode key-schedule path remains the active frontier.

The newest fd-mode traces narrowed and then reduced the frontier further:

```text
[tls13] early_secret ...
[tls13] empty_thash ...
[tls13] hs_derived ...
[tls13] handshake_secret ...
```

Using the guest's corrected `dhe_shared`, external recomputation now shows:

- `early_secret` should be the standard TLS 1.3 no-PSK constant
- `empty_thash` should be `SHA256("")`
- `hs_derived` should be the standard `derived` constant

Those are now all correct on the fd-mode path after two targeted fixes:

1. fd-mode `early_secret` is explicitly pinned to the RFC 8446 no-PSK constant because the baremetal-compiled Simple `tls13_early_secret()` path was returning all-zero bytes
2. fd-mode `hs_derived` now uses a dedicated constant-label helper because the generic dynamic-label `rt_tls13_hkdf_expand_label(..., "derived", ...)` path was producing the wrong value

The next bad value is now `handshake_secret`.

Using the corrected guest `hs_derived` and guest `dhe_shared`, an external HKDF recomputation shows `handshake_secret` should be:

```text
9844576e7f28739534b86fe015a94c273c026e5c543fcb20b1ac2a93dfd5a6d6
```

but the guest still logs a different `handshake_secret`, which moves the active frontier down to:

1. `rt_tls13_hkdf_extract(...)`
2. then the fd-mode handshake-traffic secret expansion path

Attempting to switch only the `handshake_secret` step back to the pure Simple `hkdf_extract(...)` path is not a usable workaround either: on baremetal it returns a corrupted mostly-zero value, so the baremetal-compiled Simple extract path is also not trustworthy yet.

### Latest key evidence

The rustls fixture now writes NSS-format key log lines through `SSLKEYLOGFILE`, which provide host-side ground truth:

```text
CLIENT_HANDSHAKE_TRAFFIC_SECRET ... f623f7b41a233d3f1196016386b2da4b...
SERVER_HANDSHAKE_TRAFFIC_SECRET ... 0f668cde46fab554d01388fc6e6caee4...
```

The guest still derives different values for the same connection:

```text
[tls13] client_hs_secret ...
[tls13] server_hs_secret ...
```

The guest's X25519 shared secret is now correct, but the guest-side handshake traffic secrets still diverge from both:

- the rustls key log output
- an external HKDF recomputation using the guest's own `dhe_shared` and `transcript_sh_hash`

So the remaining failure is now proven to be in the guest-side fd-mode key schedule, not just the AES-GCM/tag path.

### Files involved

- `src/os/tls13/tls13.spl`
- `src/os/tls13/record13.spl`
- `src/os/tls13/hkdf.spl`
- `src/os/tls13/key_schedule.spl`
- `examples/simple_os/arch/x86_64/boot/curve25519_ring_helper.c`
- `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`
- `examples/simple_os/arch/x86_64/tls_system_test_entry.spl`
- `test/system/os_tls_system_spec.spl`

## Recommended Next Steps

1. Instrument and compare `rt_tls13_hkdf_extract(...)` against an external HKDF recomputation for the same `hs_derived` and `dhe_shared`.
2. Instrument and compare `rt_tls13_hkdf_expand_label(...)` against an external HKDF recomputation for `"c hs traffic"` and `"s hs traffic"` using the guest's logged `transcript_sh_hash`.
3. Only if those match should the next step move down into AES-GCM/tag validation again.
