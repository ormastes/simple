# Bug Report: Baremetal TLS recv/parse path still mishandles boxed `[u8]` values after `ServerHello`

**ID:** `tls_baremetal_004`  
**Severity:** P1  
**Status:** open  
**Discovered:** 2026-04-17  
**Area:** x86_64 baremetal runtime / Cranelift compiled array layout / TLS recv/parser boundaries

## Summary

The remaining `test/system/os_tls_system_spec.spl` failure is no longer in TCP bring-up, and it is no longer at the first TLS record boundary either. The guest now:

- initializes VirtIO-net
- resolves ARP
- completes the TCP 3-way handshake to `10.0.2.2:4433`
- builds a `ClientHello` of plausible size (`162` bytes)
- sends `167` bytes on the established socket
- receives a valid first TLS record header from the rustls server
- parses the outer `ServerHello` handshake envelope as `type=2 body_len=118`

The host rustls fixture still closes with:

```text
[SERVER FAIL: unexpected end of file]
```

Serial evidence from the guest now shows two distinct facts:

1. The send-path copy bug and the recv-header boxed-byte bug were both real and are now fixed. The guest now decodes the first inbound TLS record header correctly:

```text
[tcp-send] first-bytes=0x16 0x3 0x1 0x0 0xa2 0x1 0x0 0x0
[tls13] _io_recv_record header type=22 pay_len=122
[tls13] after parse_handshake_header type=2 body_len=118
```

2. The crash has moved deeper, into `parse_server_hello(...)` or immediately after it. The guest now dies after the outer handshake envelope is parsed:

```text
[tls13] before sh slice pay_len=122 raw_len=127
[tls13] after sh slice hs_len=122
[tls13] before parse_handshake_header
[tls13] after parse_handshake_header type=2 body_len=118
[PANIC] heap exhausted
[PANIC] heap_off=0x138780 req=0xf000ff60 limit=0x10000000
```

The current strongest diagnosis is that variable-length fields in the baremetal recv/parser path are still being mishandled through boxed `[u8]` values or bad ABI/lowering around helper calls, causing a bogus large allocation request once `parse_server_hello(...)` starts walking the body.

## Reproduction

```bash
bin/simple test test/system/os_tls_system_spec.spl
```

Manual repro:

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
  -serial file:build/os/tls_system_manual_serial.log \
  -vga std \
  -device isa-debug-exit,iobase=0xf4,iosize=0x04 \
  -netdev user,id=net0,hostfwd=tcp::14433-:4433 \
  -device virtio-net-pci,netdev=net0
```

## Expected

- Plaintext TLS record should start with a valid ClientHello record prefix such as:
  - `16 03 01 00 ...`
- Host rustls fixture should continue the handshake and the guest should parse `ServerHello` fully.
- Guest should reach `[TLS HANDSHAKE COMPLETE]`.

## Actual

- Guest sends a `167`-byte record on an established TCP socket.
- Guest receives a valid `ServerHello`-sized TLS record and parses the outer handshake envelope.
- The guest then panics on a giant heap allocation while walking the `ServerHello` body.

## Technical Notes

### What is already ruled out

- VirtIO-net init and TX submission
- ARP and gateway MAC learning
- TCP active open / SYN-SYN+ACK-ACK
- fd vs socket object callsite confusion
- direct socket send/recv return-value encoding
- obvious TLS ClientHello size truncation at the old `64`-byte array cap
- first TLS record header parse on the recv path
- outer handshake envelope parse (`type=2`, `body_len=118`)

### Strongest current diagnosis

The remaining corruption is now inside `parse_server_hello(...)` or the immediate `ServerHello` post-parse path, not the TCP send bridge and not the outer record/header parser.

The strongest surviving suspects are:

1. boxed-byte or helper-ABI corruption while reading variable-length fields in `parse_server_hello(...)`
2. bad lowering around baremetal helper calls such as `rt_bytes_slice(...)` / `rt_bytes_u8_at(...)` when the sliced `ServerHello` body is reused by later parsers
3. a remaining compiled `[u8]` layout bug on C-originated arrays once deeper parser code starts copying or length-walking them

### Files involved

- `src/os/tls13/handshake13.spl`
- `src/os/tls13/tls13.spl`
- `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`
- `examples/simple_os/arch/x86_64/tls_system_test_entry.spl`
- `test/system/os_tls_system_spec.spl`

## Recommended Next Steps

1. Instrument `parse_server_hello(...)` field-by-field: `session_id_len`, `cipher_suite`, `exts_len`, `ext_type`, `ext_len`, `key_len`.
2. If the panic comes from the key-share walker, move full `ServerHello` extraction/parsing for the baremetal lane into C as a temporary containment step.
3. Inspect Cranelift lowering for C-originated `[u8]` arrays reused across helper boundaries in the x86_64 baremetal target.
