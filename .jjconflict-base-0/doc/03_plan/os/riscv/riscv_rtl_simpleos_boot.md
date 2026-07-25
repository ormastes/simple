# RISC-V RTL + SimpleOS Boot Plan

Related hardware launch plan:
`doc/03_plan/agent_tasks/riscv64_fpga_simpleos_launch.md` records the connected
FPGA inventory, RV64 softcore strategy, SimpleOS bring-up gates, and current
hardware/tool blockers.

**Date:** 2026-05-11 (updated 2026-06-06)

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
| B5 | HTTP server launch | HTTP-only prebuilt gate passing; current-source QEMU blocked |
| B6 | QEMU integration tests | HTTP/display/storage prebuilt smoke passed; current-source rebuild blocked by LLVM seed support |

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
- Production RISC-V link passes. QEMU UART smoke reaches boot idle with the
  minimal B5 HTTP launcher guarded behind `riscv_network_ready()`.

**Current boundary after B3/B5/B6:**
- The RISC-V service probe now requires VirtIO-net TX completion and packet RX
  readiness before setting `riscv_network_ready()`.
- RV64 QEMU has prebuilt smoke evidence for packet RX/TX through the boot-local
  ARP/TCP/HTTP provider, then serving `/health` and `/` over host forwarding.
  The `scripts/qemu/qemu_rv64_http_test.shs --expect-http-only --with-storage`
  path now requires a current-source build stamp by default and only accepts
  unstamped ELFs when `--allow-prebuilt-artifact` is passed. Do not treat the
  passing prebuilt ELF smoke as current-source rebuild evidence.
- This is still a narrow boot-local provider, not the full kernel TCP/IP
  netstack. The full TCP shim/netstack must become freestanding-safe before it
  replaces the boot-local path.
- B4 TLS must replace deterministic placeholder entropy before HTTPS/TLS can be
  treated as production-ready on baremetal.

### B4 Detail — TLS Baremetal

**Blocked, not complete:**
- `src/os/tls13/server.spl::tls13_accept` now reads and validates the first
  plaintext ClientHello record, sources fresh server random and ECDHE scalar
  bytes from `os.crypto.random.random_bytes`, prepares and writes the
  ServerHello plus encrypted EncryptedExtensions/Certificate/CertificateVerify/
  Finished server flight, then reads/decrypts/verifies the encrypted client
  Finished record and returns `Tls13AcceptResult.Accepted` with application
  record keys when the verify_data matches.
- `src/os/tls13/server.spl::tls13_prepare_server_handshake_from_record_for_test`
  can prepare offline X25519 ServerHello, shared secret, transcript, handshake
  secret, client/server handshake traffic keys, and the plaintext server
  EncryptedExtensions/Certificate/CertificateVerify/Finished flight plus
  decrypt-tested encrypted TLSCiphertext records, expected client Finished
  verify_data, and client/server application traffic keys from an already-read
  ClientHello record plus an explicit server scalar. This is not live accept:
  it uses deterministic test-only server random; socket reads/writes are live
  only through `tls13_accept`.
- Standalone Curve25519 RFC-vector coverage now passes for arbitrary-point
  X25519 after fixing the small-limb `u64` decode underflow tracked in
  `doc/08_tracking/bug/curve25519_smalllimb_arbitrary_point_mismatch_2026-05-13.md`.
- `src/os/kernel/net/embedded_certs.spl` now embeds an offline-generated
  self-signed Ed25519 certificate for CN=simpleos plus a runtime-compatible
  PKCS#8 private key. `get_baremetal_tls_info()` reports the material available.
- `src/os/kernel/net/tls_shim.spl` now backs RISC-V TLS time with the hardware
  timer and TLS certificate loading with embedded DER material. The RISC-V seed
  hook now mixes `cycle+time+instret` CSR jitter instead of the old LCG, but
  this is still not a production entropy source. `get_baremetal_tls_info()`
  separates material availability from `production_ready`; current blocker is
  `placeholder_entropy`.
- The x86_64 baremetal runtime `rt_rdrand` symbol now probes CPUID and retries
  the hardware RDRAND instruction before falling back to the boot-survivability
  TSC/xorshift path used on QEMU `qemu64`. This removes the old pure
  TSC/xorshift implementation from the desktop boot lane. The TLS shim now
  gates production readiness through `rt_entropy_hardware_ready()`: x86_64
  reports readiness from CPUID RDRAND support, while the RISC-V freestanding
  runtime still returns not-ready until SBI/hardware RNG support exists.

**Validation:**
- `bin/simple check` passes for `tls_shim.spl`, `embedded_certs.spl`, and
  `tls13/server.spl`; this only proves the current surfaces compile.
- `bin/simple test test/03_system/simpleos_tls_baremetal_gate_spec.spl --mode=interpreter`
  proves the current boundary explicitly: embedded cert material is available,
  `get_baremetal_tls_info()` reports available but not production-ready with
  blocker `placeholder_entropy`, an empty ClientHello record is rejected
  with `no_client_hello_record`, and a structurally valid ClientHello reaches
  the validation-only `server_crypto_pending` boundary.
- `bin/simple test test/03_system/simpleos_tls_embedded_material_spec.spl --mode=interpreter`
  proves the embedded certificate bytes build a TLS Certificate message and the
  embedded PKCS#8 key produces a 64-byte Ed25519 CertificateVerify signature.
- `bin/simple test test/03_system/simpleos_crypto_random_gate_spec.spl --mode=interpreter`
  proves the public random path stays on the CSPRNG, RISC-V no longer uses the
  old LCG seed hook, x86_64 `rt_rdrand` remains CPUID-gated on the hardware
  instruction path, and RISC-V TLS entropy remains explicitly not-ready.
- `bin/simple test test/01_unit/os/tls13/server_accept_spec.spl --mode=interpreter`
  covers record validation, explicit server-material accept flow reaching
  `client_finished_pending`, the offline handshake-material preparation shape,
  encrypted server flight record round-trips through Finished, client Finished
  verification, and accepted-context application keys. `bin/simple test
  test/01_unit/lib/crypto/curve25519_rfc7748_spec.spl
  --mode=interpreter --clean` now passes 7 RFC 7748 examples, and
  `bin/simple test test/01_unit/lib/crypto/curve25519_smalllimb_probe_spec.spl
  --mode=interpreter` proves arbitrary u-coordinate decode/encode round-trips.

**Next:** remove placeholder entropy before enabling
`tls_enabled` in the SimpleOS HTTP launcher.

### B5/B6 Detail — HTTP Launch + QEMU

**Partial 2026-05-12, updated 2026-05-13:**
- `os_main` now performs the controlled B5 handoff:
  `init_riscv_services_with_network()`, then `start_http_server_baremetal()`
  only when `riscv_network_ready()` is true. If no NIC is available it logs
  `[os_main] HTTP server deferred: network unavailable` and idles.
- `src/os/kernel/boot/http_baremetal.spl` is now a minimal boot-local HTTP
  loop over narrow `rt_io_tcp_*` externs. It avoids both the hosted std HTTP
  worker closure and `os.kernel.net.__init__` so the production RISC-V ELF can
  stay freestanding.
- `src/os/kernel/boot/tcp_baremetal_min.spl` provides boot-local strong
  `rt_io_tcp_bind`, `rt_io_tcp_accept_timeout`, `rt_io_tcp_write_text`, and
  `rt_io_tcp_close` symbols. These override the weak C fallbacks and currently
  provide listener state only.
- `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` provides weak
  no-network TCP fallbacks for the minimal HTTP launcher plus a QEMU `virt`
  PCI ECAM probe that can discover a `virtio-net-pci` NIC. Real TCP providers
  can override the weak socket symbols later with strong symbols.
- Current production link produces `build/simpleos-rv64.elf` with `os_main`,
  `start_http_server_baremetal`, and four freestanding weak-boot alias
  overrides for the boot-local `rt_io_tcp_*` symbols. The boot path now uses
  noalloc PMM/heap initialization directly instead of importing the hosted
  `riscv_boot_mem_init` closure.
- QEMU UART smoke reaches `[os_main] HTTP server deferred: network unavailable`
  and `[os_main] Entering boot idle loop`.
- QEMU UART smoke with `-device virtio-net-pci` now reaches PCI device
  discovery, assigns the legacy VirtIO I/O BAR, initializes full-size RX/TX
  rings, posts bounded RX buffers, proves TX completion with
  `[net-riscv] Network packet TX ready`, consumes RX descriptors, handles ARP
  and a minimal TCP handshake, and serves the boot-local HTTP response.
- `sh scripts/qemu/qemu_rv64_http_test.shs --elf build/simpleos-rv64.elf --expect-http-only`
  is the current executable HTTP boundary check. It proves `/health` returns
  JSON 200 and `/` returns HTML 200 over QEMU host forwarding. The default
  script mode remains the full production HTTP+HTTPS gate and still fails until
  RISC-V TLS is production-ready. Deferred mode remains available only for
  older packet-unavailable images.
- `sh scripts/qemu/qemu_rv64_http_test.shs --elf build/simpleos-rv64.elf --expect-http-only --with-display`
  now exposes QEMU `virtio-gpu-pci`, initializes the RV64 freestanding modern
  virtio-pci common/notify path, discovers an enabled scanout mode, creates the
  matching BGRA resource, attaches backing memory, and reports the dynamic
  display-service dimensions. Presentation is intentionally left to the
  canonical compositor after Draw IR/Engine2D rendering.
- `sh scripts/qemu/qemu_rv64_http_test.shs --elf build/simpleos-rv64.elf --expect-http-only --with-display --with-storage`
  now creates a QEMU raw probe disk with NVFS superblock replicas at LBA 0 and
  LBA 1, exposes it through `virtio-blk-pci`, initializes the RV64 freestanding
  legacy virtio-blk queue, completes three-descriptor sector-read requests,
  verifies the NVFS magic/version/generation fields, and requires
  `[storage-riscv] Storage service ready` plus `[fs-riscv] NVFS root superblock
  ready` (`NVFS root superblock ready`) before accepting the live HTTP smoke
  result.
- The current source-built RV64 HTTP ELF links with zero unexpected
  freestanding unresolved symbols and QEMU reaches the live HTTP marker. The
  serial log now reports `PMM OK` and `HEAP OK` before service startup. The
  QEMU memory map constants and the noalloc PMM initializer live in the
  freestanding C bridge because the previous SPL global-constant callsite
  lowered the initializer arguments to zero on the RV64 LLVM path.
- `scripts/qemu/qemu_rv32_http_test.shs` has the same `--expect-deferred` contract.
  This pass verified the script contract and syntax, but did not run RV32 QEMU
  because no current `build/simpleos-rv32.elf` kernel image was present.
- A diagnostic import of `os.kernel.net.tcp_shim` proves the intended strong
  `rt_io_tcp_*` path, but it is not yet production-linkable in the RISC-V ELF:
  the closure currently pulls unresolved netstack/runtime symbols including
  `log_info`, `rt_text_to_bytes`, `unsafe_addr_of`, `syscall`,
  `rt_x86_syscall`, and constant `.to_u32/.to_u64` helpers.

**Blocked, not complete for production:**
- The RISC-V network service now requires a QEMU `virtio-net-pci` device by
  vendor/device ID (`0x1af4:0x1000` legacy or `0x1af4:0x1041` modern), not just
  a generic PCI Ethernet class. The boot-local path now proves enough packet
  RX/TX for QEMU HTTP smoke, but it is still a narrow ARP/TCP/HTTP provider,
  not the full netstack.
- The freestanding C runtime currently handles only the minimal QEMU slirp
  traffic needed for `/health` and `/`. It is not yet a general TCP/IP stack.
- The existing full TCP shim/netstack still needs a freestanding-safe dependency
  slice before it can replace the listener-only boot shim.
- The full std HTTP worker/config/router/middleware closure remains deferred; a
  previous diagnostic promotion showed it still needs hosted/common runtime ABI
  such as dictionaries, string split/join/search, SWI/rank helpers, and
  `rt_bytes_to_text`.
- B4 TLS remains blocked by baremetal placeholder entropy.
- Storage now has a live RV64 QEMU `virtio-blk-pci` sector-read gate that
  verifies an NVFS superblock from disk. The full NVFS directory/file mount
  path is still not mounted in the production ELF. The current blocker is
  tracked in `doc/08_tracking/bug/riscv_boot_fs_full_mount_closure_2026-05-13.md`.

**Next:** mount the full NVFS directory/file path on top of the live RV64 block
superblock probe, keep TLS fail-closed until a real RISC-V entropy source
exists, then make the existing kernel TCP shim/netstack freestanding-safe by
removing its `log_info`,
`rt_text_to_bytes`, `unsafe_addr_of`, `syscall`/`rt_x86_syscall`, and
constant-conversion linker dependencies. After that, replace the minimal HTTP
loop with the full std HTTP worker once the remaining hosted runtime ABI is
present.

### Build Command

```bash
SIMPLE_BOOTSTRAP=1 src/compiler_rust/target/debug/simple native-build \
  --source build/os/generated --source src/os --source src/lib \
  --backend llvm \
  --opt-level=aggressive \
  --log on \
  --timeout 180 \
  --entry src/os/kernel/arch/riscv64/boot.spl \
  --entry-closure \
  --linker-script src/os/kernel/arch/riscv64/linker.ld \
  --target riscv64gc-unknown-none \
  -o build/simpleos-rv64.elf
```

Current HTTP-only smoke:

```bash
sh scripts/qemu/qemu_rv64_http_test.shs --elf build/simpleos-rv64.elf --expect-http-only
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
| `src/os/kernel/boot/http_baremetal.spl` | Boot-local baremetal HTTP launcher |
| `src/os/kernel/boot/tcp_baremetal_min.spl` | Boot-local strong `rt_io_tcp_*` listener symbols |
| `src/os/kernel/net/{tcp,driver,thread}_shim.spl` | Baremetal shim stubs |
| `src/lib/hardware/fpga_linux/soc_vhdl_gen.spl` | SoC VHDL generator |
| `src/compiler_rust/compiler/src/codegen/runtime_ffi.rs` | Runtime FFI declarations |
| `scripts/qemu/qemu_rv64_http_test.shs` | QEMU integration test script |

## Convergence (C1)

Requires Track A phase A7 + Track B phase B6 both complete.
Load SimpleOS ELF into K26 FPGA SoC RAM, HTTP server on real hardware.
