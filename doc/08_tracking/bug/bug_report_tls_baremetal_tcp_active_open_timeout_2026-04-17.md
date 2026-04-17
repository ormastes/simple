# Bug Report: Baremetal TLS guest cannot complete active TCP open to QEMU slirp host

**ID:** `tls_baremetal_003`  
**Severity:** P1  
**Status:** open  
**Discovered:** 2026-04-17  
**Area:** x86_64 baremetal runtime / VirtIO-net / TCP client active-open

## Summary

The remaining `test/system/os_tls_system_spec.spl` failure is now below TLS. The x86_64 baremetal guest can initialize networking, create a TCP socket, and enter the new direct client-connect path, but the client TCP active-open never reaches `ESTABLISHED`.

Current serial evidence:

```text
--- Test 2: TCP connect to 10.0.2.2:4433 ---
[tcp-connect] fd=0 port=4433
[net] ARP request sent for 10.0.2.2
[tcp-connect] using slirp gateway MAC fallback
[tcp-connect] handshake timeout state=2
connect failed: connect status 2305843009213693842
```

`state=2` is the new baremetal `TCP_SYN_SENT` state. The guest sends the SYN-side path, but no SYN+ACK is observed or processed, so the TLS handshake never starts.

## Reproduction

### System spec

```bash
bin/simple test test/system/os_tls_system_spec.spl
```

### Manual guest + host listener

```bash
src/compiler_rust/target/debug/simple native-build \
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
  -serial file:build/os/tls_manual_debug_serial.log \
  -vga std \
  -device isa-debug-exit,iobase=0xf4,iosize=0x04 \
  -netdev user,id=net0,hostfwd=tcp::14433-:4433 \
  -device virtio-net-pci,netdev=net0
```

## Expected

- Guest TCP connect should complete the 3-way handshake to `10.0.2.2:4433`.
- `tls13_connect(...)` should proceed to `ClientHello` send.
- Host rustls fixture should observe a real inbound TCP connection.

## Actual

- Guest enters the direct active-open path but times out in `TCP_SYN_SENT`.
- Host rustls fixture never logs an accepted connection.
- TLS system spec fails before any TLS handshake markers appear.

## Technical Notes

### Narrowed state

- Earlier blockers were already bypassed or fixed:
  - `x25519_base` heap panic
  - bad `tls13_connect` callsite passing a socket object instead of an fd
  - broken direct IPC method framing for `CONNECT` / `SEND` / `RECV`
- The baremetal lane now uses:
  - direct `rt_net_socket(...)`
  - direct `rt_net_connect_host_tls(...)`
  - direct `rt_net_send_bytes(...)` / `rt_net_recv_bytes(...)`

### Strong suspects

1. Baremetal VirtIO-net TX path sends the SYN frame, but slirp never accepts or answers it.
2. The hardcoded slirp L2 fallback may still be wrong for this QEMU build, despite matching common slirp docs (`10.0.2.2 is at 52:55:0a:00:02:02`).
3. `_tcp_handle_segment(...)` may still not match or process the client-side SYN+ACK correctly even if it arrives.
4. The connect return code is still raw from the baremetal FFI boundary, so error reporting in the Simple entrypoint is not yet normalized.

## Files Involved

- `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`
- `examples/simple_os/arch/x86_64/tls_system_test_entry.spl`
- `src/os/tls13/tls13.spl`
- `test/system/os_tls_system_spec.spl`

## Recommended Next Steps

1. Instrument `_tcp_send_segment(...)` and `_vnet_send_frame(...)` with destination MAC/IP/port for the SYN frame.
2. Instrument `_virtio_net_poll()` and `_tcp_handle_segment(...)` to prove whether a SYN+ACK ever arrives.
3. If no reply arrives, verify the slirp gateway L2 destination empirically and replace the fallback if needed.
4. Normalize the baremetal connect helper’s return-value encoding so the Simple caller reports real negative errno values instead of tagged raw integers.
