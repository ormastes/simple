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
- Added `scripts/linux_qemu_net_parity_bench.shs` to run the same C/Rust/Simple
  net parity benchmark inside a caller-supplied Linux QEMU guest image with
  `virtio-net-pci` and SSH forwarding. No Linux image is downloaded by the
  harness.
- The Linux QEMU harness now supports `LINUX_QEMU_DISK=virtio|nvme`,
  `LINUX_QEMU_ACCEL=kvm:tcg`, and reports whether failure is TCP port readiness
  or SSH authentication/banner readiness.
- Added `test/perf/net_driver_logic_bench.spl` for pure virtqueue arithmetic.
- Added `test/perf/ipc_l4_logic_bench.spl` for current IPC queue logic vs
  pure Simple L4-style 32-bit-word, 64-bit-word, and page-buffer models.
- Extended MIR strength reduction so power-of-two modulo lowering supports
  i64-sized constants used by queue/ring arithmetic, and added regression tests
  for net-driver-style `% 128` and 64-bit `% 1099511627776` masks.
- Added a host-native C vs Simple arithmetic parity benchmark for the same 11
  virtqueue/layout paths.

## Latest Logic Benchmark

`bin/simple run test/perf/net_driver_logic_bench.spl` completed with
`status=0`. The benchmark now covers the exported virtqueue size helpers and
the repeated deterministic layout arithmetic used by queue setup and TX/RX hot
paths.

| Logic path | Iterations | p50 ns | Total ns |
| --- | ---: | ---: | ---: |
| `virtqueue_desc_size` | 200000 | 3272 | 654575767 |
| `virtqueue_avail_size` | 200000 | 3567 | 713426842 |
| `virtqueue_used_size` | 200000 | 3394 | 678981031 |
| `virtqueue_total_size` | 200000 | 9973 | 1994683556 |
| `virtio_ring_slot_mod` | 200000 | 2520 | 504150103 |
| `virtio_used_ring_alignment` | 200000 | 5551 | 1110300060 |
| `virtio_queue_pfn_shift` | 200000 | 1993 | 398740697 |
| `virtio_descriptor_offset` | 200000 | 2043 | 408761433 |
| `virtio_buffer_offset` | 200000 | 2022 | 404565023 |
| `virtio_tx_packet_slot_pair` | 200000 | 2679 | 535845961 |
| `virtio_phys_addr_split` | 200000 | 2681 | 536358339 |

## Latest IPC/L4 Logic Benchmark

`bin/simple run test/perf/ipc_l4_logic_bench.spl` completed with `status=0`.
This is logic-only interpreter evidence, not syscall, scheduler, QEMU, or
cross-address-space timing.

| Logic path | Iterations | p50 ns | Total ns |
| --- | ---: | ---: | ---: |
| `current_ipc_manager_send_recv` | 100000 | 78653 | 7865336622 |
| `l4_inline_registers_32bit_words` | 100000 | 11215 | 1121524132 |
| `l4_inline_registers_64bit_words` | 100000 | 11461 | 1146134012 |
| `l4_buffer_transfer_4096byte` | 100000 | 10263 | 1026303872 |

The modeled L4-style paths are roughly 6.9x to 7.7x faster than the current
`IpcManager` queue send/recv logic in this interpreter sample. This supports a
pure Simple L4-style fast-path direction, but it does not prove kernel syscall
or architecture-specific performance yet.

## Compiler Optimization Evidence

`src/compiler/60.mir_opt/mir_opt/loop_strength.spl` now explicitly returns
optional results from the strength-reduction paths and scans i64 bit positions
when detecting power-of-two constants. This keeps the existing `% 2^n` to
`& (2^n - 1)` lowering valid for virtqueue/ring arithmetic beyond 32-bit
constants.

Validation:

- `bin/simple check src/compiler/60.mir_opt/mir_opt/loop_strength.spl test/unit/compiler/mir_opt/strength_reduction_spec.spl`
  passed.
- `bin/simple test test/unit/compiler/mir_opt/strength_reduction_spec.spl`
  passed: 2 examples, 0 failures.
- `bin/simple check test/perf/net_driver_logic_bench.spl test/perf/ipc_l4_logic_bench.spl`
  passed.
- `cargo build --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --release --features llvm --bin simple`
  passed, refreshing `src/compiler_rust/target/release/simple` with LLVM
  backend support.
- `src/compiler_rust/target/release/simple compile test/perf/net_driver_logic_native_bench.spl --native --backend=cranelift --cpu native --opt-level aggressive`
  passed and the resulting binary printed all 11 checksum labels.
- `src/compiler_rust/target/release/simple compile test/perf/net_driver_logic_native_bench.spl --native --backend=llvm --cpu native --opt-level aggressive`
  passed and the resulting binary printed all 11 checksum labels.

## Native C vs Simple Logic Evidence

`test/perf/run_net_driver_logic_parity_bench.shs` completed successfully. It
builds `test/perf/net_driver_logic_ref.c` with `gcc -O3 -march=native` and
`test/perf/net_driver_logic_native_bench.spl` with Simple native aggressive
optimization. C and Simple checksum labels matched for all 11 arithmetic paths.

Representative totals from the latest run:

| Logic path | C total ns | Simple native total ns |
| --- | ---: | ---: |
| `virtqueue_desc_size` | 167900 | 1104859 |
| `virtqueue_avail_size` | 182258 | 1874970 |
| `virtqueue_used_size` | 192838 | 2475706 |
| `virtqueue_total_size` | 182268 | 4070550 |
| `virtio_ring_slot_mod` | 182258 | 3523816 |
| `virtio_used_ring_alignment` | 91174 | 4781277 |
| `virtio_queue_pfn_shift` | 182248 | 2797680 |
| `virtio_descriptor_offset` | 182258 | 3193015 |
| `virtio_buffer_offset` | 187869 | 3816756 |
| `virtio_tx_packet_slot_pair` | 182227 | 4273588 |
| `virtio_phys_addr_split` | 182238 | 4054449 |

This proves checksum parity and gives a concrete optimizer target, but it does
not satisfy the "faster or equal than C/asm" requirement yet.

## Linux QEMU Attempt Evidence

Local Ubuntu qcow2 candidates were inspected to avoid a network download:

- `/home/ormastes/dev/pub/cuda_exercise/data/ubuntu_server_24.04_nvme_qemu.qcow2`
  is a 194 KiB placeholder and is not bootable.
- `/home/ormastes/dev/pub/cuda_exercise/data/ubuntu_server_24.10_nvme_qemu.qcow2`
  boots from disk in NVMe mode, but the harness timed out during SSH banner
  exchange on forwarded port `22922`.
- `/home/ormastes/dev/pub/cuda_exercise/data/ubuntu_server_nvme_qemu.qcow2`
  also boots from disk in NVMe mode, but did not provide benchmark-ready SSH
  within the timeout.

The Linux/QEMU comparison remains blocked on a guest image with reachable SSH
and benchmark prerequisites (`gcc`, `rustc`, `bash`) rather than on benchmark
harness construction.

## Completion Audit

| Prompt item | Status |
| --- | --- |
| Check current Simple network driver | Partial: PCI path verified, live HTTP still blocked |
| Check Linux on QEMU | Partial: harness added and local qcow2 images attempted; available images did not reach benchmark-ready SSH |
| Compare Simple vs Linux/QEMU perf | Missing; harness exists, but no successful Linux guest benchmark run yet |
| Benchmark each network logic function | Partial: expanded virtqueue/layout arithmetic benchmark added; live MMIO/syscall paths are not benchmarkable without working QEMU traffic |
| Optimize compiler optimization layer | Partial: MIR strength reduction now covers i64 power-of-two modulo masks and is covered by regression tests; Cranelift and LLVM native builds run the benchmark; native C comparison exposes remaining gap |
| Compare IPC with L4 | Partial: logic-only benchmark added; no syscall/QEMU benchmark yet |
| Pure Simple L4-style IPC | Partial: pure Simple model benchmarked; kernel fast path not implemented |
| Faster/equal than C/asm with SIMD | Missing: latest native arithmetic benchmark is checksum-equivalent but slower than C |
| 32-bit and 64-bit L4 optimization | Partial: 32-bit-word and 64-bit-word logic models benchmarked; no arch-specific kernel path yet |

## Next Work

1. Replace or extend the boot-local TCP provider so QEMU `/health` returns 200.
2. Run `scripts/linux_qemu_net_parity_bench.shs` with a real
   `LINUX_QEMU_IMAGE` and record C/Rust/Simple guest timings.
3. Promote the IPC/L4 model into a real kernel fast path and benchmark it
   through syscall/QEMU paths on 32-bit and 64-bit targets.
4. Extend native-code optimizer evidence beyond MIR strength reduction:
   inlining, bounds-check removal, SIMD lowering, and target-specific
   32-bit/64-bit codegen comparisons against C and assembly.
