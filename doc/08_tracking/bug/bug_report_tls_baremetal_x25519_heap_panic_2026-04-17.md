# Bug Report: Baremetal TLS Handshake Panics During X25519 Shared Secret on x86_64 QEMU

**Date:** 2026-04-17
**Bug ID:** `tls_baremetal_001`
**Status:** open
**Severity:** P1

## Summary

The remaining TLS system-test blocker is now narrowed past TCP, `ClientHello`, `ServerHello`, and `ServerHello` key-share extraction. The x86_64 baremetal guest now fails during `tls13_connect` at the X25519 shared-secret step, immediately after `ServerHello` is added to the transcript.

## Reproducers

- `test/system/os_tls_system_spec.spl`
- manual QEMU serial traces:
  - `build/tls_system_manual/serial_trace.log`
  - `build/tls_system_manual/serial3.log`
  - `build/tls_system_manual/serial2.log`

## What Is Still Green

- Hosted TLS interop remains green:
  - `test/system/os_tls_hosted_interop_basic_spec.spl`
  - `test/system/os_tls_hosted_interop_mtls_spec.spl`
- Hosted client handshake path using `TcpStream` is working.
- TLS send/recv/close transport error handling is now explicit and verified in the hosted path.

## Current Fault Evidence

Current serial trace on the x86_64 guest:

```text
[boot] TCP connection established
--- Test 3: TLS 1.3 handshake ---
[tls13] connect start host=localhost kind=fd
[tls13] after parse_handshake_header type=2 body_len=118
[tls13] after parse_server_hello cipher=4865 key_len=32
[tls13] after transcript_add serverhello
[heap] alloc sz=0xf000ff60 off_before=0x137ff0
[PANIC] heap exhausted
```

That narrows the crash to the next line after transcript update:

- `x25519(priv_key, sh.x25519_pub)`

The panic no longer occurs during:

- `ClientHello` construction
- `_io_send(...)`
- `_io_recv_record(...)`
- `parse_handshake_header(...)`
- `ServerHello` key-share extraction

## Narrowed Scope

Most likely fault domain:

- baremetal-only runtime / array allocation behavior exercised by `x25519(...)` / `x25519_smalllimb(...)`
- or a baremetal-specific implementation path reached by the shared-secret computation with the server's 32-byte X25519 key share

Less likely at this point:

- TLS record receive path
- `ServerHello` parsing
- transcript accumulation through `ServerHello`
- hosted TLS implementation

## Key File References

- TLS entrypoint:
  - `src/os/tls13/tls13.spl`
- X25519 dispatch:
  - `src/os/crypto/curve25519.spl`
- small-limb backend:
  - `src/os/crypto/curve25519_smalllimb.spl`
- baremetal allocator and array runtime:
  - `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`

## Why This Is A Separate Bug

Earlier TLS work fixed or narrowed:

- hosted TLS interop correctness
- baremetal TCP active open and send path
- `ServerHello` receive/header parsing
- baremetal `ServerHello` field extraction by moving the hot parser boundary to C helpers

Those changes did not clear the system-test lane because the remaining fault is now after `ServerHello` parse success and before handshake-secret derivation completes. This is a baremetal/runtime/X25519 shared-secret bug, not a general TLS parser or transport bug.

## Recommended Next Work

1. Instrument `x25519(...)` / `x25519_smalllimb(...)` with serial markers around the first few limb/array allocations.
2. Identify the exact allocation site that requests `0xf000ff60` in the baremetal runtime.
3. If the allocation is caused by compiled Simple crypto code, move the shared-secret step to a C helper or a baremetal-safe FFI path.
4. Add a minimized x86_64 baremetal repro that only performs X25519 shared-secret computation against a fixed 32-byte peer public key.

## Blocking Impact

This bug blocks:

- `test/system/os_tls_system_spec.spl`
- end-to-end baremetal TLS validation on x86_64 QEMU

This bug does **not** block:

- hosted TLS interop
- desktop integration
- current host-stream TLS coverage
