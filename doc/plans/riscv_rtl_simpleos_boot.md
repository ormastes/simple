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
  provides no-op `rt_free`, libc-free `rt_memcpy`/`rt_memset`, MMIO helpers,
  identity-mode `vmm_map_page`, service extern fallbacks, and a small hosted
  value ABI subset for strings, arrays, tuples, enums, scalar conversion, and
  indexing.
- `build/simpleos-rv64.elf` links as an ELF64 RISC-V executable at entry
  `0x80200000`.
- A temporary higher-level probe of `riscv_boot_mem_init -> os_main` now links
  to `build/simpleos-rv64-hosted-probe.elf`, proving the previous hosted
  value-runtime unresolveds are no longer the link blocker.

**Cleared 2026-05-12:**

1. `src/lib/nogc_async_mut/http_server/compression.spl`
   - Was: "Cannot infer field type: struct 'ANY' field 'zstd'"
   - Fixed: concrete `std.common.compress.{types,utilities,zstd,lz4}`
     imports avoid façade type erasure during entry-closure discovery.

2. `src/lib/nogc_async_mut/http_server/worker.spl`
   - Was: "Cannot infer field type: struct 'ANY' field 'flags'"
   - Fixed: flags were unused; dispatch now passes only op id, result, and
     timestamp.

**Remaining after B1: runtime execution validation**

The higher-level handoff (`riscv_boot_mem_init -> os_main`) now links in a
hosted probe after adding the freestanding value ABI subset. The production
`boot.spl` intentionally remains on the noalloc path until the hosted handoff is
QEMU-smoked for runtime behavior, because the new runtime bridge is a minimal
baremetal subset rather than the full hosted runtime.

The current noalloc boot path proves the ELF can cross module boundaries,
persist boot metadata, publish a scalar memory window, allocate raw pages,
initialize a raw heap, satisfy raw `rt_alloc`, emit byte log markers, and
publish service readiness state without triggering hosted runtime dependencies.
The hosted probe additionally proves PMM/heap/log/service code can link against
the freestanding value ABI.

**Next:** promote the hosted handoff into the production boot path behind a
controlled boot stage and run QEMU UART/runtime smoke before re-introducing
netstack, TLS, and HTTP closures.

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
- Production RISC-V link and QEMU UART smoke pass with the minimal B5 HTTP
  launcher guarded behind `riscv_network_ready()`.

**Remaining after B3:**
- The TCP/IoDriver shims compile and are ready for a live netstack, but the
  current RISC-V service probe still reports no PCI/VirtIO NIC.
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

**Partial 2026-05-12:**
- `os_main` now performs the controlled B5 handoff:
  `init_riscv_services_with_network()`, then `start_http_server_baremetal()`
  only when `riscv_network_ready()` is true. If no NIC is available it logs
  `[os_main] HTTP server deferred: network unavailable` and idles.
- `src/os/kernel/net/http_baremetal.spl` is now a minimal kernel-native HTTP
  loop over narrow `rt_io_tcp_*` externs. It avoids the hosted std HTTP worker
  closure so the production RISC-V ELF can link without weak freestanding
  stubs.
- `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` provides weak
  no-network TCP fallbacks for the minimal HTTP launcher plus a QEMU `virt`
  PCI ECAM probe that can discover a `virtio-net-pci` NIC. Real TCP providers
  can override the weak socket symbols later with strong symbols.
- Normal production link produces `build/simpleos-rv64.elf` with `os_main`,
  `riscv_boot_mem_init`, `start_http_server_baremetal`, and weak `rt_io_tcp_*`
  fallback symbols present.
- QEMU UART smoke reaches `[os_main] HTTP server deferred: network unavailable`
  and `[os_main] Entering boot idle loop`.
- QEMU UART smoke with `-device virtio-net-pci` reaches
  `[net-riscv] Network probe passed`, starts `start_http_server_baremetal()`,
  then stops at `[http_baremetal] ERROR: bind failed` because the actual TCP
  provider is still the weak no-network fallback.
- A diagnostic import of `os.kernel.net.tcp_shim` proves the intended strong
  `rt_io_tcp_*` path, but it is not yet production-linkable in the RISC-V ELF:
  the closure currently pulls unresolved netstack/runtime symbols including
  `log_info`, `rt_text_to_bytes`, `unsafe_addr_of`, `syscall`,
  `rt_x86_syscall`, and constant `.to_u32/.to_u64` helpers.

**Blocked, not complete for production:**
- The RISC-V network service can now discover a QEMU `virtio-net-pci` device,
  but `rt_io_tcp_bind()` is still the weak no-network fallback in the production
  RISC-V ELF, so the QEMU HTTP test cannot yet prove an actual socket response.
- The existing strong TCP shim needs a freestanding-safe dependency slice before
  it can override the weak C TCP fallbacks in the production RISC-V link.
- The full std HTTP worker/config/router/middleware closure remains deferred; a
  previous diagnostic promotion showed it still needs hosted/common runtime ABI
  such as dictionaries, string split/join/search, SWI/rank helpers, and
  `rt_bytes_to_text`.
- B4 TLS remains blocked by the placeholder TLS 1.3 server surface.

**Next:** bind the kernel TCP shim/netstack into the freestanding RISC-V link
with strong `rt_io_tcp_*` symbols, then run the QEMU HTTP socket smoke. After
that, replace the minimal HTTP loop with the full std HTTP worker once the
remaining hosted runtime ABI is present.

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
| `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` | Freestanding allocation/value ABI bridge |
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
