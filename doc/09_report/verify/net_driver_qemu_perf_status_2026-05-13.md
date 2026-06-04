# SimpleOS Network Driver / QEMU / Perf Status - 2026-05-13

Scope: incremental evidence for the network-driver/QEMU/performance request.

## Evidence

- The RV32/RV64 HTTP QEMU scripts present in this checkout use
  `virtio-net-pci`, matching the current PCI-oriented SimpleOS virtio-net
  probe.
- RV64 QEMU reaches `Network service ready` and
  `Bootstrap TCP shim bound on 0.0.0.0:8080`; host HTTP probes still fail
  after bind because the boot-local TCP provider does not accept traffic.
- `src/os/kernel/boot/tcp_baremetal_min.spl` is the active boot provider, and
  `rt_io_tcp_accept_timeout()` returns `-1`.
- `test/perf/net_driver_logic_bench.spl` now benchmarks 11 pure virtqueue and
  layout arithmetic paths.
- `test/perf/ipc_l4_logic_bench.spl` compares current IPC queue logic with
  pure Simple L4-style 32-bit, 64-bit, and 4096-byte transfer models.
- `src/compiler/60.mir_opt/mir_opt/loop_strength.spl` now detects i64-sized
  power-of-two modulo constants, with regression coverage in
  `test/unit/compiler/mir_opt/strength_reduction_spec.spl`.
- `src/compiler_rust/compiler/src/codegen/llvm/backend_core.rs` now lowers
  Simple function attributes `@inline`, `@always_inline`, and `@force_inline`
  to LLVM `alwaysinline` function attributes.
- `test/perf/run_net_driver_logic_parity_bench.shs` builds a C reference with
  `gcc -O3 -march=native` and a Simple native binary, then verifies checksum
  parity for all 11 arithmetic paths.

## Net Driver Logic Benchmark

`bin/simple run test/perf/net_driver_logic_bench.spl` completed with
`status=0`.

| Logic path | Iterations | p50 ns | Total ns |
| --- | ---: | ---: | ---: |
| `virtqueue_desc_size` | 200000 | 3455 | 691187119 |
| `virtqueue_avail_size` | 200000 | 3587 | 717572185 |
| `virtqueue_used_size` | 200000 | 3556 | 711284632 |
| `virtqueue_total_size` | 200000 | 10160 | 2032198650 |
| `virtio_ring_slot_mod` | 200000 | 2608 | 521612470 |
| `virtio_used_ring_alignment` | 200000 | 5671 | 1134310719 |
| `virtio_queue_pfn_shift` | 200000 | 2052 | 410484981 |
| `virtio_descriptor_offset` | 200000 | 1837 | 367519379 |
| `virtio_buffer_offset` | 200000 | 1953 | 390764085 |
| `virtio_tx_packet_slot_pair` | 200000 | 2754 | 550962488 |
| `virtio_phys_addr_split` | 200000 | 2375 | 475084170 |

## IPC/L4 Logic Benchmark

`bin/simple run test/perf/ipc_l4_logic_bench.spl` completed with `status=0`.
This is logic-only interpreter evidence, not syscall, scheduler, QEMU, or
cross-address-space timing.

| Logic path | Iterations | p50 ns | Total ns |
| --- | ---: | ---: | ---: |
| `current_ipc_manager_send_recv` | 100000 | 84755 | 8475590693 |
| `l4_inline_registers_32bit_words` | 100000 | 11458 | 1145846993 |
| `l4_inline_registers_64bit_words` | 100000 | 11643 | 1164338761 |
| `l4_buffer_transfer_4096byte` | 100000 | 10241 | 1024133481 |

The modeled L4-style paths are roughly 7.3x to 8.3x faster than current
`IpcManager` queue send/recv logic in this sample.

## Native C vs Simple Logic Evidence

`SIMPLE_BIN=src/compiler_rust/target/release/simple
test/perf/run_net_driver_logic_parity_bench.shs` completed successfully.
C and Simple checksum labels matched for all 11 arithmetic paths.

| Logic path | C total ns | Simple native total ns |
| --- | ---: | ---: |
| `virtqueue_desc_size` | 103978 | 558507 |
| `virtqueue_avail_size` | 108347 | 574577 |
| `virtqueue_used_size` | 108337 | 557004 |
| `virtqueue_total_size` | 108357 | 1649020 |
| `virtio_ring_slot_mod` | 108347 | 55807 |
| `virtio_used_ring_alignment` | 20 | 919467 |
| `virtio_queue_pfn_shift` | 54203 | 102676 |
| `virtio_descriptor_offset` | 103949 | 51749 |
| `virtio_buffer_offset` | 108347 | 51498 |
| `virtio_tx_packet_slot_pair` | 119459 | 77869 |
| `virtio_phys_addr_split` | 30 | 110040 |

Simple native is faster than C on 4 of 11 standalone paths in this run
(`ring`, `descriptor`, `buffer`, `tx_pair`). C still wins the remaining paths,
including cases where C optimized the whole loop into a near-constant result.

## Validation

- `cargo check -p simple-compiler` passed.
- `cargo build --release -p simple-native-all` passed.
- `bin/simple check src/compiler/60.mir_opt/mir_opt/loop_strength.spl
  test/unit/compiler/mir_opt/strength_reduction_spec.spl
  test/perf/net_driver_logic_bench.spl
  test/perf/ipc_l4_logic_bench.spl
  test/perf/net_driver_logic_native_bench.spl` passed.
- `bin/simple test test/unit/compiler/mir_opt/strength_reduction_spec.spl`
  passed: 2 examples, 0 failures.
- `bash -n test/perf/run_net_driver_logic_parity_bench.shs
  scripts/qemu/qemu_rv64_http_test.shs scripts/qemu/qemu_rv32_http_test.shs` passed.

## Completion Audit

| Prompt item | Status |
| --- | --- |
| Check current Simple network driver | Partial: PCI path verified, live HTTP still blocked |
| Check Linux on QEMU | Missing in this checkout: no working Linux guest benchmark run completed |
| Compare Simple vs Linux/QEMU perf | Missing: no successful Linux guest benchmark evidence |
| Benchmark each network logic function | Partial: 11 pure arithmetic paths covered; live MMIO/syscall paths still need working QEMU traffic |
| Optimize compiler optimization layer | Partial: i64 MIR strength reduction and LLVM inline attrs added; C parity still has gaps |
| Compare IPC with L4 | Partial: logic-only benchmark added; no syscall/QEMU benchmark yet |
| Pure Simple L4-style IPC | Partial: pure Simple model benchmarked; kernel fast path not implemented |
| Faster/equal than C/asm with SIMD | Missing: Simple is faster than C on 4/11 measured arithmetic paths, no asm/SIMD comparison yet |
| 32-bit and 64-bit L4 optimization | Partial: 32-bit-word and 64-bit-word logic models benchmarked; no arch-specific kernel path yet |

## Next Work

1. Replace or extend the boot-local TCP provider so QEMU `/health` returns 200.
2. Add or restore a Linux QEMU guest parity harness, then run it with a guest
   image that has reachable SSH and compiler prerequisites.
3. Promote the IPC/L4 model into a real kernel fast path and benchmark it
   through syscall/QEMU paths on 32-bit and 64-bit targets.
4. Extend optimizer work into bounds-check removal, vectorization/SIMD
   lowering, and target-specific comparison against C and assembly.
