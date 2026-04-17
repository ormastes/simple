# Bug Report: Baremetal TLS Handshake Panics in `x25519_base` on x86_64 QEMU

**Date:** 2026-04-17
**Bug ID:** `tls_baremetal_001`
**Status:** open
**Severity:** P1

## Summary

The remaining TLS system-test blocker is no longer in hosted TLS, record decrypt, or post-handshake app-data flow. The x86_64 baremetal guest now fails earlier: during `tls13_connect`, inside the `x25519_base` step, before `ClientHello` construction completes.

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
[tls13] before x25519_base
[heap] alloc sz=0xf000ff60 off_before=0x7080
[PANIC] heap exhausted
```

That narrows the crash to the pre-read handshake path, specifically before:

- `build_client_hello_bytes(...)`
- `_build_plaintext_record(...)`
- `_io_send(...)`
- `_io_recv_record(...)`

The panic therefore occurs before any ServerHello parsing or fd receive logic can execute.

## Narrowed Scope

Most likely fault domain:

- baremetal-only runtime / array allocation behavior exercised by X25519 on the guest
- or a baremetal-specific implementation path reached by `x25519_base(...)`

Less likely at this point:

- TLS record receive path
- ServerHello parsing
- transcript hashing
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
- hosted TLS perf split
- transport-result handling for `tls13_send`, `tls13_recv`, `tls13_close`
- several parser and length-trust hazards in TLS helpers

Those changes did not clear the system-test lane because the remaining fault happens before the first network read and before `ClientHello` send completion. This is now a baremetal/runtime/X25519 bug, not a general TLS state-machine bug.

## Recommended Next Work

1. Instrument `x25519_base(...)` and the selected backend with serial markers at function entry/exit and around any array allocations or conversions.
2. Instrument the baremetal runtime allocation helpers in `baremetal_stubs.c` for array growth / array creation call sites used by crypto code.
3. Confirm whether the guest is entering `x25519_base_smalllimb(...)` and identify the exact first allocation above `0x100000`.
4. If the fault is in the runtime rather than crypto math, create a minimized x86_64 baremetal probe that calls only `x25519_base(...)`.

## Blocking Impact

This bug blocks:

- `test/system/os_tls_system_spec.spl`
- end-to-end baremetal TLS validation on x86_64 QEMU

This bug does **not** block:

- hosted TLS interop
- desktop integration
- current host-stream TLS coverage
