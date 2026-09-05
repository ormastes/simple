<!-- codex-design -->

# SimpleOS QEMU VirtIO-serial host-GPU transport gap

Date: 2026-07-30
Reviewed revision: `9cd238428b4ea0c1481c153cae66b8b017629994`

## Status

`BLOCKED` for x86_64 and RISC-V.

The current wrapper correctly reports `virtio-serial-unimplemented` when
`ivshmem-plain` and the AArch64-only file-backed RAM tail are unavailable but
QEMU exposes `virtio-serial-pci` or `virtio-serial-device`. Do not weaken that
classification. No source in `src/os/` implements a VirtIO console device or a
framed host-GPU port, and `simpleos_gpu_host` accepts only `--shm` plus the
fixed AArch64 `--shm-offset`.

The plan's current capability checkpoint records VirtIO serial as the only
candidate host-offload transport for the x86_64 and RISC-V rows. This review
did not launch QEMU or repeat that capability probe. AArch64 file-backed RAM
tail is a distinct, already-scoped transport and is not evidence for either
x86_64 or RISC-V.

## Current owners and missing boundary

| Owner | Current behavior | Gap |
|---|---|---|
| `scripts/check/check-simpleos-qemu-host-gpu-2d.shs` | Classifies `ivshmem-plain`, AArch64 file-backed RAM tail, and `virtio-serial-unimplemented`; launches the daemon with `--shm`. | No socket endpoint, VirtIO-serial QEMU argv, readiness receipt, or framed-evidence validation. |
| `src/os/kernel/ipc/host_gpu_ivshmem_map.spl` | Maps QEMU ivshmem BAR2 only. | Must remain ivshmem-specific; it must not pretend a byte-stream port is MMIO. |
| `src/os/lib/gpu_bridge/host_gpu_ivshmem.spl` | Writes the canonical control page/payload, publishes a generation, busy-polls completion, and returns an MMIO readback address. | The protocol operation is coupled to random-access MMIO and cannot send or receive a framed stream. |
| `src/os/compositor/engine2d_wm_frame_executor.spl` | Negotiates and submits directly through ivshmem functions, then presents from `receipt.output_addr`. | Needs a composed host-GPU session/transport owner; serial readback must land in guest-owned aligned memory before presentation. |
| `src/lib/common/gpu/simpleos_host_gpu_protocol.spl` | Owns protocol v1 validation, generation, run/frame correlation, backend identity, bounded payload/readback sizes, and checksums. | Needs a transport-neutral request/response model and stream envelope codec without changing v1 rendering semantics. |
| `src/app/simpleos_gpu_host/daemon_runner.spl` | mmaps an 8 MiB file and polls its single request slot. | Needs a UNIX-domain socket endpoint and an executor function that consumes a decoded request rather than an mmap base. |
| `test/03_system/os/qemu/simpleos_qemu_host_gpu_2d_spec.spl` | Proves the current ivshmem contract and wrapper fail-closed behavior. | Needs framed-codec, endpoint, per-ISA device/queue, timeout, and classifier-transition assertions. |

## Required architecture

Keep the shared rendering protocol authoritative and add adapters around it:

```text
Engine2dWmFrameExecutor
        |
        v
SimpleOsHostGpuSession (one negotiated session, one request in flight)
        |
        +-- IvshmemHostGpuTransport (existing MMIO behavior)
        |
        `-- VirtioSerialHostGpuTransport
                +-- x86_64 VirtIO PCI transport
                `-- RISC-V VirtIO MMIO transport

QEMU virtserialport byte stream
        |
        v
SimpleOsGpuHostSocketEndpoint -> shared request executor -> host GPU
```

The session owns negotiation, monotonically increasing generation, stable
positive `run_id_hash`, per-request positive `frame_id`, retained-image state,
and fail-closed reset. The transport owns only delivery and readback storage.
The renderer must not acquire device queues or parse frames.

Add transport-neutral values in
`src/lib/common/gpu/simpleos_host_gpu_protocol.spl`:

- `SimpleOsHostGpuRequest`: all current HELLO/DRAW_IR/PROCESSING fields,
  correlation tuple, payload bytes, and image-resource bytes.
- `SimpleOsHostGpuResponse`: status/reason, negotiated values or device
  receipt, exact correlation tuple, and readback bytes.
- validation and execution stay shared; ivshmem and stream adapters encode the
  same values. Existing wire offsets and protocol version 1 remain unchanged.

## Framed stream contract

Every integer is unsigned little-endian on the stream. Each logical message
starts with one fixed 64-byte header:

| Offset | Width | Field |
|---:|---:|---|
| 0 | 4 | stream magic `SHGF` |
| 4 | 2 | stream envelope version (`1`) |
| 6 | 2 | header bytes (`64`) |
| 8 | 2 | type: HELLO request/response, SUBMIT request/response, or ERROR response |
| 10 | 2 | flags; must be zero in version 1 |
| 12 | 4 | body byte count |
| 16 | 4 | body checksum |
| 20 | 4 | reserved; must be zero |
| 24 | 8 | request generation |
| 32 | 8 | session `run_id_hash` (`0` only for HELLO request/response) |
| 40 | 8 | frame ID (`0` only for HELLO request/response) |
| 48 | 8 | backend code |
| 56 | 8 | request kind for requests; status/reason packing for responses |

The body is the canonical request or response codec, not a native struct dump.
It has explicit field order and lengths followed by payload/image-resource or
readback bytes. The decoder rejects bad magic/version/header size, nonzero
reserved bits, unknown type, overflow, truncated/extra bytes, invalid enum,
oversized payload/readback, checksum mismatch, and a correlation tuple that
does not exactly match the sole outstanding request.

`body_bytes` is bounded before allocation by the existing 64 KiB payload and
`simpleos_host_gpu_max_readback_bytes()` limits. The byte stream may split a
logical frame across any number of VirtIO descriptors. Both endpoints use a
64 KiB bounded scratch buffer and incremental checksum; readback streams
directly into one aligned guest-owned buffer. No queue descriptor or socket
read is assumed to equal a frame.

Only one request may be outstanding. A response is accepted only when
`(generation, run_id_hash, frame_id, backend_code, message_type)` exactly
matches the pending request. Duplicate, future, late, or cross-session frames
close/reset the transport, clear retained resources, and require a new HELLO.

## QEMU and host endpoint

The wrapper must create a private socket path inside its per-run build
directory, start `simpleos_gpu_host --socket=<path>`, wait for an explicit
`HOST_GPU_DAEMON_SOCKET_READY` receipt, and then launch QEMU as the socket
client. It must record the encoded argv and socket-mode receipt but never
record socket contents as a substitute for correlated device readback.

x86_64 uses a dedicated controller and port:

```text
-device virtio-serial-pci,id=hostgpu-serial
-chardev socket,id=hostgpu,path=<path>,server=off,reconnect-ms=100
-device virtserialport,bus=hostgpu-serial.0,nr=1,chardev=hostgpu,name=org.simple.hostgpu
```

RISC-V uses the same port contract over VirtIO MMIO:

```text
-device virtio-serial-device,id=hostgpu-serial
-chardev socket,id=hostgpu,path=<path>,server=off,reconnect-ms=100
-device virtserialport,bus=hostgpu-serial.0,nr=1,chardev=hostgpu,name=org.simple.hostgpu
```

The wrapper must verify these devices in `-device help` before selecting the
new transport. It may return `virtio-serial-framed` only after the guest
artifact attests the matching adapter and the socket endpoint passes its
focused tests. Otherwise the existing `virtio-serial-unimplemented` result
remains mandatory.

`SimpleOsGpuHostSocketEndpoint` owns listen/accept, exact-length partial
send/receive loops, connection deadline, frame decoding, and one client.
`SimpleOsGpuHostRequestExecutor` owns validation, backend execution, retained
resources, and response construction. An endpoint/framing failure drops the
connection and session state; it must not fall back to CPU or synthesize PASS.

## Queue and interrupt ownership

`VirtioSerialHostGpuPort` is the sole owner of the VirtIO console device and
all its descriptors:

- control RX/TX queues negotiate `DEVICE_READY`, discover the port by exact
  name `org.simple.hostgpu`, send `PORT_READY`, and require `PORT_OPEN`;
- the named port's RX/TX queues carry framed bytes; queue numbers come from
  the negotiated port ID and are never hardcoded from QEMU argv;
- the x86_64 adapter owns PCI discovery/configuration and interrupt
  registration for console device IDs; the RISC-V adapter owns scanning the
  QEMU `virtio-mmio` slots and its PLIC interrupt registration;
- queue memory is DMA-safe, aligned, bounded, and private to the driver. One
  descriptor chain is owned by exactly one queue until its used-ring entry is
  consumed. RX buffers are reposted only after their bytes are copied or
  streamed to the final readback buffer.

The architecture IRQ handler acknowledges the device and marks used control
or data queues ready; it does not parse protocol frames or execute rendering.
The driver/session task drains queues and wakes the waiting WM submitter.
Bounded polling is allowed only in the direct-boot probe before interrupts and
the scheduler are active, and must be separately identified in evidence.
Production WM uses interrupts.

The session lock serializes negotiation and submit. Backpressure is one
logical request, one response, and bounded RX/TX descriptor pools—never an
unbounded software queue.

## Timeouts and failure policy

- HELLO retains the existing 500,000 us end-to-end budget.
- A submitted render/processing request retains the existing 5,000,000 us
  end-to-end budget.
- Queue waits and host socket I/O use the same absolute monotonic deadline,
  not independent retry budgets.
- The host stops work and discards an unsent response after its request
  deadline. The guest drops any later response by exact correlation.
- Disconnect, EOF, port close, used-ring stall, checksum failure, oversize,
  malformed control event, or deadline expiry returns a non-PASS receipt,
  clears retained resources, and forces HELLO before another submit.
- No transport failure may be reported as device readback, Metal/Vulkan
  success, or AArch64 coverage.

## Implementation and test decomposition

1. **Common codec**
   - Add `src/lib/common/gpu/simpleos_host_gpu_stream_protocol.spl`.
   - Unit-test round trips, partial input, every malformed header class,
     overflow/oversize, checksum, and stale/cross-session correlation.
2. **Shared daemon executor**
   - Extract request execution from
     `src/app/simpleos_gpu_host/daemon_runner.spl` without changing ivshmem
     behavior.
   - Add socket endpoint and bounded exact-I/O adapter using the existing
     UNIX-socket runtime facade; test partial reads/writes, EOF, timeout,
     reconnect, retained-state reset, and one-in-flight enforcement.
3. **Guest VirtIO console core**
   - Add `src/os/drivers/virtio/virtio_console.spl` plus a
     `src/os/lib/gpu_bridge/host_gpu_virtio_serial.spl` adapter.
   - Synthetic-ring tests cover control handshake, dynamic port ID, descriptor
     ownership, split/coalesced frames, IRQ wakeup, queue exhaustion, and
     bounded early-boot polling.
4. **x86_64 adapter**
   - Add PCI discovery/config/IRQ ownership and a focused freestanding probe.
   - Attest `virtio-serial-pci`, exact named-port QEMU argv, HELLO, correlated
     render response, checksum, device readback, timeout, and disconnect.
5. **RISC-V adapter**
   - Add `virtio-mmio` console discovery/PLIC ownership and a focused
     freestanding probe.
   - Attest `virtio-serial-device` with the same protocol and negative gates.
6. **WM integration**
   - Compose `SimpleOsHostGpuSession` into
     `Engine2dWmFrameExecutor`; place serial readback into aligned guest-owned
     memory and retain the existing framebuffer checksum/presentation gate.
   - Keep software fallback honest and retain the per-frame generation/run/
     frame receipts.
7. **Wrapper/system evidence**
   - Extend the wrapper classifier only after the adapters exist.
   - Add source assertions and socket-loop integration scenarios to
     `simpleos_qemu_host_gpu_2d_spec.spl`.
   - Add one bounded live x86_64 row and one bounded live RISC-V row proving
     exact QEMU argv, port readiness, HELLO, later correlated device frame,
     checksum, dimensions, ordered event-triggered later frame, timeout
     rejection, and cleanup. Q-LIVE remains the sole QEMU executor.

## Acceptance gates

- Current ivshmem and AArch64 file-backed-tail tests remain unchanged and
  green.
- The codec and socket endpoint have no unbounded length or retry path.
- x86_64 and RISC-V each prove their own adapter, device, queue/interrupt
  owner, and correlated readback; neither inherits AArch64 evidence.
- `virtio-serial-unimplemented` remains until all source, artifact, and live
  gates for that row pass.
- No CPU fallback, scanout-only image, serial marker alone, or source-only
  assertion can satisfy a live host-GPU row.

## Bounded source-only checks

Executed exactly once in the isolated clean worktree:

```text
PASS  sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test-qemu-accel
      simpleos_qemu_host_gpu_2d_qemu_accel_self_test=pass

BLOCKED  SIMPLE_LIB=src bin/simple test test/03_system/os/qemu/simpleos_qemu_host_gpu_2d_spec.spl --mode=interpreter
         zsh:1: no such file or directory: bin/simple
```

The interpreter spec was not retried because this checkout has no admitted
`bin/simple`, and this delegated lane forbids bootstrap. This environmental
blocker does not change the transport finding.
