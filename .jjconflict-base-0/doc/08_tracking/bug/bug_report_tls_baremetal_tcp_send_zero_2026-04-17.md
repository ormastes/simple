# Bug Report: Baremetal TLS guest reports TCP connect success but never sends ClientHello

**Bug ID:** `tls_baremetal_002`  
**Date:** 2026-04-17  
**Reporter:** Codex  
**Priority:** P1  
**Status:** Open  
**Component:** Baremetal TCP/netstack path (`src/os/userlib/net.spl`, `src/os/tls13/tls13.spl`, x86_64 QEMU guest networking)

## Summary

After working around the earlier baremetal `x25519_base` heap failure, the x86_64 TLS system guest now reaches `ClientHello` construction but still fails the live handshake because the service-managed TCP path never produces a real outbound send. The guest reports TCP connect success, then `_io_send` observes `wrote=0`, and a host listener bound to `0.0.0.0:4433` never receives an accept or payload from the guest.

This is a distinct bug from `tls_baremetal_001`: the remaining blocker is now the baremetal TCP connect/send state machine or userspace send ABI, not the earlier X25519 heap panic.

## Reproduction

### System spec

```bash
bin/simple test test/system/os_tls_system_spec.spl
```

Observed result:

```text
[os_tls_system_spec] [TLS HANDSHAKE COMPLETE] not seen within 60s
```

### Manual guest + host listener

1. Start a host TCP listener bound to all interfaces on port `4433`.
2. Boot the baremetal guest:

```bash
qemu-system-x86_64 \
  -kernel build/os/simpleos_tls_system_x86_64.elf \
  -m 2G -nographic -monitor none -no-reboot \
  -netdev user,id=net0 -device virtio-net-pci,netdev=net0 -vga std
```

3. Inspect guest serial log.

Observed guest serial markers before the TLS callsite fix:

```text
[boot] TCP connection established
[tls13] connect start host=localhost kind=fd
[tls13] before build_client_hello
[tls13] after build_client_hello len=64
[tls13] after build_plaintext_record len=64
[tls13] _io_send start kind=fd len=64
[tls13] _io_send loop sent=0 total=64
[tls13] _io_send chunk_len=64
[tls13] _io_send wrote=0
[tls13] after transcript_add clienthello
[tls13] _io_recv_record start
[tls13] _io_recv request len=5 kind=fd
[tls13] _io_recv chunk_len=0
...
```

The `tls13_connect` callsite in `examples/simple_os/arch/x86_64/tls_system_test_entry.spl` was also wrong and has since been fixed:

```spl
val tls_result = tls13_connect(tcp_sock.fd.to_i64(), "localhost")
```

Observed guest serial markers after the callsite fix:

```text
[boot] TCP connection established
[tls13] connect start host=localhost kind=fd
[tls13] before build_client_hello
[tls13] after build_client_hello len=64
[tls13] after build_plaintext_record len=64
[tls13] _io_send start kind=fd len=64
[tls13] _io_send loop sent=0 total=64
[tls13] _io_send chunk_len=64
[tls13] _io_send wrote=0
[tls13] _io_send send err
[TLS FAIL: handshake failed: ClientHello send failed]
```

Observed host behavior:

- Listener bound to `0.0.0.0:4433` never accepts a connection from the guest.
- No TLS bytes arrive on the host.

## Expected

- Guest TCP connect should only report success once the TCP connection is actually established.
- `send()` on the connected socket should either:
  - return a positive byte count, or
  - return an explicit error / would-block signal.
- Host listener should accept the guest connection and receive the `ClientHello`.

## Actual

- Guest-side connect path reports success early.
- TLS fd send path sees `wrote=0`.
- Host never sees an incoming connection or payload.
- TLS handshake now fails fast on `ClientHello send failed`.

## Technical Notes

### Narrowed state

- `tls_baremetal_001` was worked around enough that the guest no longer dies before `ClientHello`.
- The public X25519 share in `tls13_connect` is now precomputed because the private key is fixed.
- The baremetal bump heap was increased to keep the X25519 ladder from immediately exhausting the stub allocator during the system lane.

### Strong suspects

1. **Service-managed connect/send state mismatch**
   - `src/os/userlib/net.spl` opens and connects sockets through the syscall/netstack service path.
   - After the `tls13_connect` callsite bug was fixed, `send()` still returns `0` for a non-empty `ClientHello`.
   - A host listener still never accepts a connection, so the netstack-side socket likely never reaches a truly established outbound state even though `connect()` reports success.

2. **Userspace send ABI mismatch**
   - `src/os/userlib/net.spl` currently does:
     ```spl
     syscall(75, sock.fd as u64, data_ptr, data.len() as u64, 0, 0)
     ```
   - This has been tightened to pass the array data pointer instead of the array-object header, but the behavior did not change in the live baremetal TLS lane.
   - That suggests the remaining fault is deeper than the raw pointer shape alone.

3. **Runtime direct-socket helpers are a different fd namespace**
   - Temporary instrumentation with `rt_net_send_bytes()` showed `EBADF fd=0 state=0`.
   - That helper operates on the baremetal runtime `_sockets[]` table, while `os.userlib.net` uses the syscall/netstack service socket namespace.
   - So `rt_net_send_bytes()` is useful for diagnosis but is not a valid fallback for this bug.

4. **FD TLS path assumes POSIX-style send semantics**
   - `_io_send()` in `src/os/tls13/tls13.spl` expects `send()` to return bytes written.
   - The baremetal socket path may need a readiness poll or a different ABI contract.

## Files Involved

- `src/os/tls13/tls13.spl`
- `src/os/userlib/net.spl`
- `src/os/posix/socket_compat.spl`
- `src/os/services/netstack/netstack_service.spl`
- `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`
- `test/system/os_tls_system_spec.spl`

## Recommended Next Steps

1. Instrument the netstack-service-backed connect/send path to log the actual socket state transition and whether a SYN/SYN-ACK/ACK exchange completes before `connect()` returns.
2. Audit the syscall `73/75/76` forwarding path against `src/os/services/netstack/netstack_service.spl` to confirm the service-managed socket id and send semantics used by baremetal match the hosted lane.
3. Make baremetal `connect()` expose readiness honestly or add a poll/wait-for-established helper before TLS sends its first record.
4. Once the host listener sees a real `ClientHello`, rerun:
   - `bin/simple test test/system/os_tls_system_spec.spl`
   - hosted TLS interop specs to ensure no regression in shared TLS logic.
