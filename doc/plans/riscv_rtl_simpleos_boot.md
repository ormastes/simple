# RISC-V RTL + SimpleOS Boot Plan

**Date:** 2026-05-11 (updated 2026-05-12)

## Goal

Production-level RISC-V system:
1. CPU RTL written in Simple (.spl) → VHDL via compiler backend
2. Three deployment layers: GHDL simulation → QEMU virt → Kria K26 FPGA
3. SimpleOS boots with HTTP + TLS + auth/RBAC server stack

## Track A: RTL CPU + SoC — Status

| Phase | Description | Status |
|-------|-------------|--------|
| A1 | RV32I core in .spl RTL | DONE |
| A2 | M-mode CSR + trap handling | DONE (in SoC gen) |
| A3 | SoC peripherals (UART, CLINT, bootrom) | DONE |
| A4 | Wishbone bus + SoC top + testbench | DONE (`af7af19`) |
| A5 | PLIC + interrupt routing | Not started |
| A6 | MMU (Sv32/Sv39) | Not started |
| A7 | RV64 widening + K26 FPGA | Not started |
| A8 | Ethernet MAC | Not started |

**A1-A4 proven:** GHDL simulation runs 49 cycles, outputs "SimpleOS\n", halts.

## Track B: SimpleOS QEMU Boot — Status

| Phase | Description | Status |
|-------|-------------|--------|
| B1 | Boot entry + freestanding cross-link | DONE |
| B2 | TCP shim | DONE |
| B3 | IoDriver shim | DONE |
| B4 | TLS on baremetal | BLOCKED |
| B5 | HTTP server launch | BLOCKED |
| B6 | QEMU integration tests | BLOCKED |

### B1 Detail — Current Blockers

**Done:**
- Runtime FFI fix: all `rt_*` declared for all targets (was excluding Sys/Async)
- `os_main.spl`: removed broken `boot_fs` dependency
- `width_index.spl`: `me` → `self` parse fix for `--entry-closure` discovery
- Identified correct build flags: `--entry-closure` + `--linker-script`
- HTTP compression enum inference fixed by importing concrete compression
  modules instead of the broad façade.
- HTTP worker completion inference fixed by removing unused
  `completion.flags` access from the dispatch path.
- Freestanding `_init_all.cpp` generation now compiles with the requested
  cross target, fixing the host `_init_all.o` vs `elf64-littleriscv` mismatch.
- RISC-V `_start` now calls the entry-closure mangled boot symbol
  `kernel__arch__riscv64__boot__boot_main` instead of the stale `os__...`
  symbol.
- B1 boot entry now stays truly freestanding: `_start` clears BSS, calls
  `boot_main`, writes the UART banner, records a noalloc scalar boot handoff,
  and halts without pulling hosted PMM, heap, logging, netstack, or HTTP
  closures.
- `src/os/kernel/boot/riscv_noalloc_handoff.spl` provides the first
  cross-module boot handoff that is still freestanding-safe: it captures hart
  id, DTB address, RAM bounds, and a reserved heap window using only scalar
  globals and byte UART output (`MEM OK`). The final boot idle marker is
  emitted only after PMM and heap initialization (`OS IDLE`).
- `src/os/kernel/boot/riscv_noalloc_pmm.spl` adds a freestanding scalar PMM
  window over RAM between the reserved kernel/image prefix and the upper heap
  reservation. It exposes raw 4 KiB page allocation without bitmap arrays,
  `Option`, logging, MMIO wrappers, or hosted runtime helpers.
- `src/os/kernel/boot/riscv_noalloc_heap.spl` adds a freestanding raw bump heap
  over the reserved upper 16 MiB RAM window. This is a boot heap surface only;
  it is not yet wired to the hosted `rt_alloc` value ABI.
- `src/os/kernel/boot/riscv_noalloc_log.spl` adds byte-only UART log markers
  (`LOG OK`, `BOOT OK`) without importing the hosted log facade or formatted
  `text` runtime.
- `src/os/kernel/boot/riscv_noalloc_services.spl` adds a scalar boot-service
  readiness snapshot for memory/SPM/network/display/storage state without IPC
  objects, arrays, `text`, or runtime PCI/display/network externs.
- `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` is compiled as a
  RISC-V boot object and bridges `rt_alloc` to the noalloc heap. It also
  provides no-op `rt_free` plus libc-free `rt_memcpy`/`rt_memset`, so raw
  struct allocation can link without hosted malloc.
- `build/simpleos-rv64.elf` links as an ELF64 RISC-V executable at entry
  `0x80200000`.

**Cleared 2026-05-12:**

1. `src/lib/nogc_async_mut/http_server/compression.spl`
   - Was: "Cannot infer field type: struct 'ANY' field 'zstd'"
   - Fixed: concrete `std.common.compress.{types,utilities,zstd,lz4}`
     imports avoid façade type erasure during entry-closure discovery.

2. `src/lib/nogc_async_mut/http_server/worker.spl`
   - Was: "Cannot infer field type: struct 'ANY' field 'flags'"
   - Fixed: flags were unused; dispatch now passes only op id, result, and
     timestamp.

**Remaining after B1: hosted OS/runtime ABI handoff**

Re-enabling the higher-level handoff (`riscv_boot_mem_init -> os_main`) pulls
hosted-style PMM/heap/log/service code and still fails on missing freestanding
runtime symbols beyond raw allocation, such as `rt_string_new`, `rt_array_push`,
`rt_enum_new`, `rt_native_eq`, `rt_mmio_read_u64`, and `log_raw_println`. Adding
`--source src/runtime` does not resolve this; the missing piece is either a
RISC-V-linkable Simple runtime ABI for that value model or narrower noalloc
service/net/HTTP shims. The current noalloc boot path proves the ELF can cross
module boundaries, persist boot metadata, publish a scalar memory window,
allocate raw pages, initialize a raw heap, satisfy raw `rt_alloc`, emit byte log
markers, and publish service readiness state without triggering hosted runtime
dependencies.

**Next:** either bridge hosted arrays, `text`, enum values, and formatted
logging to a freestanding runtime ABI, or continue carving noalloc net/HTTP
entry points that avoid the hosted value model before re-introducing netstack,
TLS, and HTTP closures.

### B2/B3 Detail — TCP + IoDriver Shims

**Done 2026-05-12:**
- `net_boot_init()` now creates the cooperative `NetstackService` singleton
  after the C-backed VirtIO-net probe succeeds.
- `src/os/kernel/net/tcp_shim.spl` now delegates bind, accept, connect, read,
  write, and close to the live netstack when it is initialized, while keeping
  the previous state-only fallback for early boot/pre-network calls.
- `src/os/kernel/net/driver_shim.spl` now drives pending accept/recv operations
  through the TCP shim during `rt_driver_poll()` instead of leaving them
  permanently pending.
- `rt_driver_poll_data()` and `rt_driver_poll_data_len()` accept either the
  poll batch index or the completion op id, matching the existing HTTP worker
  call pattern.

**Validation:**
- `bin/simple check` passes for `tcp_shim.spl`, `driver_shim.spl`,
  `driver_shim_state.spl`, `netstack_init.spl`, and
  `http_server/worker.spl`.
- B1 freestanding RISC-V link still passes after the shim changes.

**Remaining after B3:**
- The higher-level OS handoff still needs the freestanding runtime/noalloc
  boundary described above before these shims can be included in the boot ELF.
- B4 TLS must replace deterministic placeholder entropy/time/file behavior
  before TLS can be treated as production-ready on baremetal.

### B4 Detail — TLS Baremetal

**Blocked, not complete:**
- `src/os/tls13/server.spl::tls13_accept` still returns
  `Tls13AcceptResult.Failed("not_implemented")`; the TLS 1.3 server-side record
  I/O loop, key exchange, transcript, CertificateVerify, Finished, and app
  secret derivation are not wired.
- `src/os/kernel/net/embedded_certs.spl` contains placeholder DER-like byte
  sequences, not a real offline-generated certificate/key pair.
- `src/os/kernel/net/tls_shim.spl` still uses deterministic placeholder
  entropy/time/file behavior for baremetal.

**Validation:**
- `bin/simple check` passes for `tls_shim.spl`, `embedded_certs.spl`, and
  `tls13/server.spl`; this only proves the current placeholder surfaces compile.

**Next:** implement or reuse a real TLS server handshake surface before enabling
`tls_enabled` in the SimpleOS HTTP launcher.

### B5/B6 Detail — HTTP Launch + QEMU

**Blocked, not complete:**
- `src/os/kernel/net/http_baremetal.spl` exists, but enabling it from the
  RISC-V boot path pulls the full HTTP worker/config/router/middleware closure.
- That closure still depends on the hosted value/runtime ABI unless the
  noalloc boundary is completed first.
- B6 QEMU HTTP tests cannot be meaningful until B5 can be linked into the
  boot ELF.

**Current safe artifact:**
- The B1 ELF intentionally remains a freestanding UART-banner boot artifact:
  `build/simpleos-rv64.elf`.

**Next:** extend the freestanding noalloc boundary from raw PMM/heap metadata
to log/service handoff and hosted allocation ABI, then re-enable
`riscv_boot_mem_init -> os_main -> http_baremetal` and run the QEMU HTTP smoke.

### Build Command

```bash
SIMPLE_BOOTSTRAP=1 src/compiler_rust/target/debug/simple native-build \
  --source src/os --source src/lib \
  --entry src/os/kernel/arch/riscv64/boot.spl \
  --entry-closure \
  --linker-script src/os/kernel/arch/riscv64/linker.ld \
  --target riscv64gc-unknown-none \
  -o build/simpleos-rv64.elf
```

## Key Files

| File | Role |
|------|------|
| `src/os/kernel/arch/riscv64/boot.spl` | Entry: `_start → boot_main` |
| `src/os/kernel/boot/riscv_noalloc_handoff.spl` | Freestanding scalar boot handoff |
| `src/os/kernel/boot/riscv_noalloc_pmm.spl` | Freestanding raw page allocator |
| `src/os/kernel/boot/riscv_noalloc_heap.spl` | Freestanding raw bump heap |
| `src/os/kernel/boot/riscv_noalloc_log.spl` | Freestanding byte log markers |
| `src/os/kernel/boot/riscv_noalloc_services.spl` | Freestanding service readiness snapshot |
| `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` | Freestanding raw allocation bridge |
| `src/os/kernel/boot/riscv_boot_mem.spl` | PMM + heap init |
| `src/os/kernel/boot/os_main.spl` | Service init → HTTP server |
| `src/os/kernel/arch/riscv64/linker.ld` | Linker script (0x80200000) |
| `src/lib/nogc_async_mut/http_server/` | Async HTTP server (21 files) |
| `src/os/kernel/net/http_baremetal.spl` | Baremetal HTTP launcher |
| `src/os/kernel/net/{tcp,driver,thread}_shim.spl` | Baremetal shim stubs |
| `src/lib/hardware/fpga_linux/soc_vhdl_gen.spl` | SoC VHDL generator |
| `src/compiler_rust/compiler/src/codegen/runtime_ffi.rs` | Runtime FFI declarations |
| `scripts/qemu_rv64_http_test.shs` | QEMU integration test script |

## Convergence (C1)

Requires Track A phase A7 + Track B phase B6 both complete.
Load SimpleOS ELF into K26 FPGA SoC RAM, HTTP server on real hardware.
