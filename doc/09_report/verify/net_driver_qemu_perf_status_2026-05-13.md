# SimpleOS Network Driver / QEMU / Perf Status — 2026-05-13

Scope: incremental evidence for the network-driver/QEMU/performance request.

## Evidence

- The QEMU RV32/RV64 HTTP scripts now use `virtio-net-pci`, which matches the
  current PCI-oriented SimpleOS virtio-net probe.
- RV64 QEMU with `virtio-net-pci` reaches `Network service ready` and
  `Bootstrap TCP shim bound on 0.0.0.0:8080`.
- Host HTTP probes still return `000`; the serial log confirms this is after
  bind, so the blocker is host-visible TCP/HTTP response handling.
- `src/os/kernel/boot/tcp_baremetal_min.spl` is the active boot provider, and
  `rt_io_tcp_accept_timeout()` always returns `-1`.
- Host Linux loopback parity for 5000 iterations / 1024-byte payload:
  `bin/simple`: C 212067 us, Rust 200955 us, Simple 206258 us.
  Rebuilt release sample: C 183066 us, Rust 190505 us, Simple 189390 us.
- Added `test/perf/net_driver_logic_bench.spl` for pure virtqueue arithmetic.

## Latest Logic Benchmark

`bin/simple run test/perf/net_driver_logic_bench.spl` completed with
`status=0`.

| Logic path | Iterations | p50 ns | Total ns |
| --- | ---: | ---: | ---: |
| `virtqueue_desc_size` | 200000 | 3673 | 734756854 |
| `virtqueue_avail_size` | 200000 | 3651 | 730392585 |
| `virtqueue_used_size` | 200000 | 3646 | 729229883 |
| `virtqueue_total_size` | 200000 | 10998 | 2199608244 |
| `virtio_ring_slot_mod` | 200000 | 2780 | 556113240 |

## Completion Audit

| Prompt item | Status |
| --- | --- |
| Check current Simple network driver | Partial: PCI path verified, live HTTP still blocked |
| Check Linux on QEMU | Missing |
| Compare Simple vs Linux/QEMU perf | Missing; host Linux loopback only |
| Benchmark each logic function | Partial: first virtqueue logic set added |
| Optimize compiler optimization layer | Missing |
| Compare IPC with L4 | Missing |
| Pure Simple L4-style IPC | Missing |
| Faster/equal than C/asm with SIMD | Missing |
| 32-bit and 64-bit L4 optimization | Missing |

## Next Work

1. Replace or extend the boot-local TCP provider so QEMU `/health` returns 200.
2. Add Linux guest baseline automation using the same QEMU topology.
3. Add 32-bit and 64-bit IPC/L4-style microbenchmarks.
4. Revisit compiler inlining/SIMD only after native hot-path evidence.
