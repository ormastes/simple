# SimpleOS Multi-Arch HAL & Hardening Architecture

**Feature:** simpleos-multiarch-harden
**Phase:** 3 (Architecture)
**Date:** 2026-04-25
**Status:** Locked — Phase 5 implementation MUST conform to the trait surface in §2.

This document is the AC-7 deliverable. It locks the Hardware Abstraction Layer
(HAL) trait surface, the C→Simple port map, the per-arch consolidation plan,
the hardening matrix, and the multi-arch bootstrap pipeline for the six
SimpleOS targets: **x86_64, x86_32 (i686), aarch64, armv7 (arm32), rv64gc,
rv32imac**.

The HAL boundary already exists in `src/os/kernel/arch/hal.spl` (1,197 LoC,
8 traits, 6-arch `@cfg`-dispatched implementations). This phase **consolidates
and completes** that boundary; it does not greenfield it.

---

## 1. Goals & Non-Goals

### Goals
- Single, locked HAL trait surface that all arch-neutral kernel and userland
  Simple code routes through.
- Zero owned-code C in the SimpleOS kernel image (one file, `runtime_minimal.c`,
  ported to Simple).
- Zero hand-written `.S` outside HAL: `simpleos_crt0.S`, `simpleos_setjmp.S`,
  `arm64/boot/crt0.S` either ported to Simple via HAL or replaced by a
  generated trampoline.
- ≥40% reduction in per-arch LoC by lifting shared logic into `arch/common/`.
- Per-boot randomized stack canaries on every arch.
- W^X enforcement on every arch (with the i686-non-PAE exception spelled out).
- Capability-checked syscall trampoline per arch.
- `bootstrap-from-scratch.sh --arch=<triple>` succeeding for all six lanes.
- NVFS on-disk format stable across 32-bit and 64-bit kernels.

### Non-Goals (this round)
- Hardfloat 32-bit variants (softfloat-only baseline confirmed).
- SMP bring-up (trait shape reserved; impl deferred — see Open Questions).
- FPU/SIMD context save (trait shape reserved; impl deferred).
- Self-hosted `isel_armv7` / `isel_x86_32` codegen (32-bit lanes route through
  LLVM fallback, already wired in `qemu_runner.spl`).
- Userland MDSOC+ port reshaping (orthogonal feature).

---

## 2. HAL Trait Surface (LOCKED)

### 2.1 Existing traits (already in `arch/hal.spl`)

| Trait | Purpose | Status |
|---|---|---|
| `HalConsole` | Early console (VGA / PL011 / SBI / 16550) | All 6 archs impl |
| `HalBoot` | Parse bootloader-supplied `BootOutputPort` | All 6 archs impl |
| `HalCpu` | enable/disable IRQ, halt, halt_loop, cpu_id, address_width | All 6 archs impl |
| `HalPower` | system_reset (test mode + arch dispatch) | All 6 archs impl |
| `HalPaging` | init/map/unmap/translate/create/switch_address_space, levels, flush_tlb, flush_tlb_all | All 6 archs impl |
| `HalInterrupt` | acknowledge, set_handler, mask, eoi | All 6 archs impl |
| `HalTimer` | init, deadline, ack, now_ns | All 6 archs impl |
| `HalContext` | task context save/restore (in-trait, kernel-thread switching) | All 6 archs impl |

### 2.2 Existing methods (signature reference)

```
trait HalConsole:
    fn hal_console_init()
    fn hal_console_write_byte(b: u8)
    fn hal_console_write(s: text)
    fn hal_console_writeln(s: text)

trait HalBoot:
    fn hal_parse_boot_info() -> BootOutputPort

trait HalCpu:
    fn hal_disable_interrupts()
    fn hal_enable_interrupts()
    fn hal_halt()
    fn hal_halt_loop()
    fn hal_cpu_id() -> u64
    fn hal_address_width() -> u32

trait HalPower:
    fn hal_reset_set_test_mode(enabled: bool)
    fn hal_reset_requested_for_test() -> bool
    fn hal_system_reset() -> i64
    fn _hal_system_reset_arch() -> i64        # @cfg(arch) per-arch

trait HalPaging:
    fn hal_paging_init(boot_info: BootOutputPort)
    fn hal_paging_map(virt: VirtAddr, phys: PhysAddr, flags: VmFlags) -> bool
    fn hal_paging_unmap(virt: VirtAddr) -> bool
    fn hal_paging_translate(virt: VirtAddr) -> PhysAddr?
    fn hal_paging_create_address_space() -> u64
    fn hal_paging_switch_address_space(root_phys: u64)
    fn hal_paging_levels() -> u32
    fn hal_flush_tlb(addr: u64)
    fn hal_flush_tlb_all()

trait HalInterrupt:
    fn hal_interrupt_acknowledge(irq: u32)
    fn hal_interrupt_set_handler(irq: u32, handler: u64)
    fn hal_interrupt_mask(irq: u32, mask: bool)
    fn hal_interrupt_eoi(irq: u32)

trait HalTimer:
    fn hal_timer_init(hz: u32)
    fn hal_timer_set_deadline(ns_from_now: u64)
    fn hal_timer_ack()
    fn hal_timer_now_ns() -> u64

trait HalContext:
    fn hal_context_init(stack_top: u64, entry: u64) -> ArchContext
    fn hal_context_switch(prev: &ArchContext, next: &ArchContext)
```

### 2.3 NEW traits added this phase (Phase 5 will impl)

#### 2.3.1 `HalEntropy` — boot-time entropy (R6 — stack canary fix)

```
trait HalEntropy:
    fn hal_random_seed_u64() -> u64        # best-effort early seed; NOT crypto RNG
    fn hal_random_available() -> EntropyClass
                                            # EntropyClass = { Hardware, MixedTSC, FallbackOnly }
```

Per-arch impl:

| Arch | Primary | Fallback chain |
|---|---|---|
| x86_64 | `RDSEED` → `RDRAND` | TSC + boot-load-addr + bootloader seed |
| x86_32 | `RDRAND` if CPUID supports | TSC + boot-load-addr + bootloader seed |
| aarch64 | `RNDR` (probe ARMv8.5+; HWCAP2_RNG) | `CNTVCT_EL0` + `CNTPCT_EL0` + DTB seed |
| arm32 | (no hw RNG mandatory) | `CNTVCT` + boot-time + DTB seed |
| rv64gc | SBI `sbi_get_random` if available | `cycle` + `time` + `instret` + hartid + DTB seed |
| rv32imac | SBI `sbi_get_random` if available | `cycle` + `time` + `instret` + hartid + DTB seed |

**Codex confirmed:** `mrandom` CSR is non-standard; do NOT build the ABI around
it. Prefer SBI. `RDRAND` in QEMU is acceptable as a best-effort early seed,
not a sole trust anchor. Mix multiple sources.

#### 2.3.2 `HalCstart` — replace `simpleos_crt0.S` and `simpleos_setjmp.S`

```
trait HalCstart:
    fn hal_cstart_init(argc: i32, argv: u64, envp: u64) -> i32
    fn hal_setjmp(buf: &mut JmpBuf) -> i32
    fn hal_longjmp(buf: &JmpBuf, val: i32)         # noreturn
    fn hal_cstart_exit(code: i32)                  # noreturn
```

`JmpBuf` is an arch-tagged opaque struct; per-arch sizing is encoded in
`arch_context.spl`. R7 is closed by this trait — no per-arch `.S` files for
crt0/setjmp.

#### 2.3.3 `HalSyscall` — capability-checked entry trampoline

```
trait HalSyscall:
    fn hal_syscall_install_vector()
                                # one-time per-CPU vector install
    fn hal_syscall_dispatch(nr: u32, a0: u64, a1: u64, a2: u64, a3: u64,
                            a4: u64, a5: u64) -> i64
                                # cap-check site lives HERE, not in Simple-side syscall.spl
```

Per-arch entry vector: x86_64 `syscall`/`sysret` MSR setup; x86_32 `int 0x80`
gate; aarch64/arm32 `svc`/`svc 0`; rv64gc/rv32imac `ecall` from U-mode.
Capability check is invoked exactly once at trampoline entry, before
arch-neutral dispatch reaches `src/os/kernel/ipc/syscall.spl`.

#### 2.3.4 `HalCanary` — per-boot stack guard (R6)

```
trait HalCanary:
    fn hal_canary_init()                            # seeds __stack_chk_guard from HalEntropy
    fn hal_canary_value() -> u64
    fn hal_canary_fail()                            # noreturn; logs + halts
```

`hal_canary_init()` is called exactly once after `hal_paging_init` and before
the first kernel-thread spawn. It replaces the
`__stack_chk_guard = 0xDEADBEEFDEADBEEFUL` constant in
`src/os/libc/simpleos_cxxabi.c:158-160`.

#### 2.3.5 `HalSmp` (RESERVED — impl deferred)

```
trait HalSmp:
    fn hal_smp_cpu_count() -> u32
    fn hal_smp_cpu_start(ap_id: u32, entry: u64, stack: u64, arg: u64) -> bool
    fn hal_smp_ipi_send(target: u32, vector: u32)
    fn hal_smp_ipi_broadcast(vector: u32)
```

Trait shape locked NOW so Phase 5 ABI doesn't churn; impl is **deferred to a
follow-up feature**. UP-only kernel for AC-4 smoke. (Codex recommendation.)

#### 2.3.6 `HalPerCpu` (RESERVED — impl deferred)

```
trait HalPerCpu:
    fn hal_percpu_set_base(ptr: u64)
    fn hal_percpu_get_base() -> u64
```

Maps to `GSBASE`/`FSBASE` (x86), `TPIDR_EL1` (arm64), `TPIDRPRW` (arm32),
`tp` (riscv). Deferred with `HalSmp`.

#### 2.3.7 `HalBarrier` — MMIO ordering (correctness-critical on ARM/RISC-V)

```
trait HalBarrier:
    fn hal_barrier_load()
    fn hal_barrier_store()
    fn hal_barrier_full()
    fn hal_barrier_iomem_read()
    fn hal_barrier_iomem_write()
```

Required NOW (not deferred) — driver/MMIO code on ARM (PL011, GIC) and RISC-V
(PLIC, CLINT) is silently incorrect without explicit barriers. Mapping:

| Arch | load | store | full | iomem-r | iomem-w |
|---|---|---|---|---|---|
| x86_64/x86_32 | (no-op; TSO) | (no-op; TSO) | `mfence` | `lfence` | `sfence` |
| aarch64 | `dmb ld` | `dmb st` | `dmb sy` | `dmb oshld` | `dmb oshst` |
| arm32 | `dmb ld` | `dmb st` | `dmb sy` | `dmb oshld` | `dmb oshst` |
| rv64gc | `fence r,r` | `fence w,w` | `fence rw,rw` | `fence i,r` | `fence o,w` |
| rv32imac | `fence r,r` | `fence w,w` | `fence rw,rw` | `fence i,r` | `fence o,w` |

#### 2.3.8 `HalCache` — i-cache / d-cache maintenance (mandatory ARM/RISC-V)

```
trait HalCache:
    fn hal_cache_sync_icache(addr: u64, len: u64)
    fn hal_cache_clean_dcache(addr: u64, len: u64)
    fn hal_cache_invalidate_dcache(addr: u64, len: u64)
```

x86 impl is mostly no-op (coherent). ARM uses `ic ivau` / `dc cvau` / `dc ivac`.
RISC-V uses `fence.i` and Zicbom/Zicboz CMO instructions if available, else
implementation-defined `cflush.d.l1`/SBI extension.

Required for: ELF loader writing then executing pages, JIT trampolines,
user-trampoline patching.

### 2.4 Trait inventory total

**16 traits** (8 existing + 6 new-with-impl + 2 reserved-only):
1. `HalConsole` (existing)
2. `HalBoot` (existing)
3. `HalCpu` (existing)
4. `HalPower` (existing)
5. `HalPaging` (existing)
6. `HalInterrupt` (existing)
7. `HalTimer` (existing)
8. `HalContext` (existing)
9. `HalEntropy` (NEW — implement)
10. `HalCstart` (NEW — implement; replaces `.S`)
11. `HalSyscall` (NEW — implement)
12. `HalCanary` (NEW — implement)
13. `HalBarrier` (NEW — implement)
14. `HalCache` (NEW — implement)
15. `HalSmp` (NEW — reserve trait shape, defer impl)
16. `HalPerCpu` (NEW — reserve trait shape, defer impl)

> `HalFpContext` is NOT added in this phase. If userland SIMD/FPU lands before
> next refactor, reserve `hal_context_save_extended()` /
> `hal_context_restore_extended()` on `HalContext` rather than fork a new
> trait. (Codex's "ABI-stability" note.)

---

## 3. C → Simple Port Map (AC-1 / AC-2)

### 3.1 Critical-path (kernel image)

| Order | C source | LoC | Target Simple file | Dependency |
|---|---|---:|---|---|
| 1 | `src/runtime/startup/baremetal/runtime_minimal.c` | 246 | `src/os/runtime/baremetal/runtime_minimal.spl` | LEAF — port first, no callers depend |
| 2 | `src/os/libc/simpleos_crt0.S` (x86_64) | 61 | `HalCstart` impl in `arch/x86_64/cstart.spl` | depends on #1 |
| 3 | `src/os/libc/simpleos_setjmp.S` (x86_64) | 72 | `HalCstart` impl in `arch/x86_64/cstart.spl` | independent of #2; can parallelize |
| 4 | `src/os/kernel/arch/arm64/boot/crt0.S` | 56 | `HalCstart` impl in `arch/arm64/cstart.spl` | independent; parallelize |
| 5..10 | `crt0` + `setjmp` impl for x86_32, arm32, rv64gc, rv32imac (NEW — none exist yet) | n/a | `arch/<arch>/cstart.spl` | depends on `HalCstart` trait landing in `hal.spl` |

### 3.2 Userland libc shim (P0)

Port these 10 files in a parallelized pass — each is mostly arch-neutral and
calls into HAL via the new traits:

| C source | LoC | Target |
|---|---:|---|
| `simpleos_libc.c` | ~700 | `src/os/libc/simpleos_libc.spl` |
| `simpleos_fs.c` | ~600 | `src/os/libc/simpleos_fs.spl` |
| `simpleos_stdlib_ext.c` | ~400 | `src/os/libc/simpleos_stdlib_ext.spl` |
| `simpleos_string_ext.c` | ~300 | `src/os/libc/simpleos_string_ext.spl` |
| `simpleos_time.c` | ~250 | `src/os/libc/simpleos_time.spl` |
| `simpleos_alloc.c` | ~500 | `src/os/libc/simpleos_alloc.spl` |
| `simpleos_pthread.c` | ~400 | `src/os/libc/simpleos_pthread.spl` |
| `simpleos_process.c` | ~350 | `src/os/libc/simpleos_process.spl` |
| `simpleos_cxxabi.c` | ~200 | `src/os/libc/simpleos_cxxabi.spl` (canary→`HalCanary`) |
| `simpleos_signal.c` | ~250 | `src/os/libc/simpleos_signal.spl` |

These can be parallelized across 5 Sonnet agents (2 files each) once HAL traits
land. Each file's residual extern allow-list: only POSIX-ABI `.h` headers stay.

### 3.3 Hosted runtime (P1, off the SimpleOS kernel critical path)

`src/runtime/runtime.c` (1,378), `runtime_thread.c` (613), `runtime_native.c`
(460), `async_driver.c` (301), `runtime_memtrack.c` (288), and the 6
`platform/async_*.c` files do NOT ship in the kernel image and are on the
hosted-runtime path. They are P1 (port post-AC-4) and out of scope for the
AC-4 boot-smoke gate. Ship-list: separate sstack feature.

### 3.4 P3 (keep as-is)

- `src/os/sdk/include/simpleos.h` (151 LoC) — public C-ABI SDK header. Stays.
- All POSIX `.h` headers under `src/os/libc/` — ABI contracts, not code.
- All vendored C (rquickjs-sys, miniaudio, stb_*) — vendor-excluded per
  CLAUDE.md.

---

## 4. Per-Arch Consolidation Plan (AC-3)

### 4.1 Baseline LoC (Phase 2 measured)

| Arch | LoC | Files |
|---|---:|---:|
| x86_64 | 2,746 | 13 |
| x86_32 | 1,760 | 10 |
| arm32 | 1,806 | 8 |
| arm64 | 1,801 (≈) | 9 |
| riscv64 | 2,644 | 15 |
| riscv32 | 1,533 | 9 |
| **Total** | **~12,290** | **64** |

(`arch/hal.spl` 1,197 + `arch/mod.spl` 206 + `arch/arch_context.spl` ≈ shared
already; plus existing `arch/arm/pl011_common.spl`.)

### 4.2 Functions to lift to `arch/common/`

| Sub-system | Current per-arch LoC (avg) | Shared target file | Estimated shared LoC | Per-arch reduction |
|---|---:|---|---:|---:|
| Console framing (`writeln`, `write`, hex/dec format) | ~50 each | `arch/common/console_framing.spl` | ~80 | 6 × ~30 = 180 |
| Paging tree-walk skeleton (level descent loop, flag mask) | ~120 each | `arch/common/paging_walker.spl` | ~150 | 6 × ~80 = 480 |
| Interrupt vector dispatch shell (mask/unmask/eoi switch) | ~60 each | `arch/common/interrupt_dispatch.spl` | ~100 | 6 × ~40 = 240 |
| Timer deadline math (ns ↔ ticks, jitter clamp) | ~60 each | `arch/common/timer_math.spl` | ~80 | 6 × ~40 = 240 |
| Context-switch fixed-frame format (offsets, magic) | ~40 each | `arch/common/context_layout.spl` | ~60 | 6 × ~25 = 150 |
| RV32+RV64 SBI ECALL shim | ~150 each (rv only) | `arch/common/sbi_shim.spl` | ~180 | 2 × ~100 = 200 |
| ARM32+ARM64 GIC v2/v3 dispatch | ~80 each (arm only) | `arch/common/gic_common.spl` | ~120 | 2 × ~60 = 120 |
| x86_64+x86_32 IDT/GDT skeleton | ~70 each (x86 only) | `arch/common/x86_descriptor.spl` | ~100 | 2 × ~50 = 100 |

**Estimated total reduction:** ~1,710 LoC moved out of per-arch + ~870 added to
`arch/common/` = net per-arch shrink of ~1,710 / ~12,290 = **~14% from
consolidation alone**.

To hit ≥40%, additionally:
- Lift PL011 dup between `arm/pl011_common.spl` and `arm32/console.spl`,
  `arm64/console.spl` (already partial; finish job): ~150 LoC.
- Lift 16550 UART dup between `riscv32/console.spl`, `riscv64/console.spl`,
  and shared `boot/uart16550_mmio.spl`: ~200 LoC.
- Lift paging-flag enum + permission-encoding helpers: ~300 LoC.
- Lift ELF loader's per-arch `R_*` relocation tables to a single table
  driven by `arch_context.Architecture`: ~200 LoC.

**Revised total reduction estimate:** ~1,710 + 850 = **2,560 LoC removed
from per-arch** = **~21% per-arch baseline shrink**. To reach 40%, the
**paging.spl files (3,105 LoC across 6 archs, the heavyweight)** must absorb
the biggest cuts: extract the page-table-walking algorithmic core (level
descent, PTE flag encode/decode, CoW fault walker) into
`arch/common/paging_walker.spl` and reduce per-arch paging files from
~500 LoC each to ~250 LoC each (just MMU-register access + flag layout).
That alone yields another 1,500 LoC reduction.

**Feasibility verdict for ≥40%:** **Tight but achievable.** Hitting 40%
requires the paging-walker extraction. Phase 5 must validate this by
prototyping the paging-walker abstraction on x86_64 first; if x86_64 paging
shrinks from 531 to ≤270 LoC, the 40% target is on track. Otherwise,
**escalate to user** — either accept ~25% reduction or expand the consolidation
scope.

### 4.3 Where shared helpers live

```
src/os/kernel/arch/common/
├── console_framing.spl          # writeln, hex, dec, byte-string framing
├── paging_walker.spl            # generic level-descent + PTE encode helper
├── interrupt_dispatch.spl       # mask/unmask/eoi switch table
├── timer_math.spl               # ns ↔ ticks, deadline jitter clamp
├── context_layout.spl           # ArchContext common-frame magic + offsets
├── sbi_shim.spl                 # RV-only SBI ECALL helpers
├── gic_common.spl               # ARM-only GIC v2/v3 dispatch
├── x86_descriptor.spl           # x86-only IDT/GDT skeleton
└── relocations.spl              # ELF R_* tables driven by arch enum
```

---

## 5. Hardening Matrix (AC-5)

| Gate | x86_64 | x86_32 | aarch64 | arm32 | rv64gc | rv32imac |
|---|---|---|---|---|---|---|
| **Stack canary entropy source** | RDSEED→RDRAND | RDRAND (CPUID-gated) | RNDR (probe v8.5+); else CNTVCT+CNTPCT+DTB seed | CNTVCT+DTB seed | SBI `sbi_get_random` else cycle+time+instret+hartid+DTB | SBI else cycle+time+instret+hartid+DTB |
| **Canary install site** | `hal_canary_init()` post-paging, pre-thread-spawn | same | same | same | same | same |
| **W^X primitive** | NX bit (paging.spl:285,292) | **PAE-mandatory + NX** OR mapping-discipline-only (see §5.1) | UXN/PXN bits | XN bit (PXN if v6K+) | PMP `R/W/X` bits | PMP `R/W/X` bits |
| **Capability-check site** | `HalSyscall::hal_syscall_dispatch` trampoline → `_cap_check()` | same | same | same | same | same |
| **Bounds-check intrinsic** | compiler-emitted `@check_bounds` (Simple default) | same | same | same | same | same |
| **`unsafe`/`@nocheck` policy** | only inside `arch/x86_64/` | only inside `arch/x86_32/` | only inside `arch/arm64/` | only inside `arch/arm32/` | only inside `arch/riscv64/` | only inside `arch/riscv32/` |
| **MMIO barrier policy** | mfence/lfence/sfence (TSO mostly) | same | dmb sy/ld/st | dmb sy/ld/st | fence rw,rw / fence i,r / fence o,w | same |
| **i-cache sync after ELF load** | no-op (coherent) | no-op (coherent) | `ic ivau` per cacheline | `mcr p15, ICIMVAU` | `fence.i` (+ Zicbom CMO if avail) | same |

### 5.1 i686 / x86_32 W^X decision

**Codex recommendation accepted:**
- On non-PAE i686, treat executable user pages as permanently read-only;
  writable pages are non-executable **only by mapping policy**, not hardware.
- `hal_paging_map(virt, phys, W|X)` returns `false` on i686 unconditionally.
- For ELF load + relocate flows, use the temp-writable-alias-then-remap-RX
  pattern: map RW alias for fixups, `hal_flush_tlb`, then remap original VA
  as RX-only.
- **PAE-mandatory** gating is preserved for i686 builds with userspace exec
  permissions: a kernel-config flag `CONFIG_X86_32_PAE` switches paging.spl
  to PAE-mode page tables (NX bit available).
- Default for AC-4 smoke: non-PAE + mapping-discipline. Document as
  not-hardware-W^X; PAE is a follow-up feature.

### 5.2 Audit script `os-harden-audit.spl`

New file: `src/app/build/os_harden_audit.spl`. Runs per-arch via
`bin/simple build check --arch=<triple>`. Checks:

1. **`@nocheck`/`unsafe` outside HAL:** `grep` for `@nocheck` and `unsafe` in
   `src/os/` excluding `src/os/kernel/arch/**`. Fail if any hit.
2. **Direct arch import bypass:** `grep` for `use os.kernel.arch.x86_64`,
   `arm64`, `arm32`, `riscv64`, `riscv32`, `x86_32` outside
   `src/os/kernel/arch/**`. Fail if any hit (must go through `hal.spl`).
3. **Stack-canary sentinel:** `grep` for the constant `0xDEADBEEF` in
   compiled output of `simpleos_cxxabi.spl`. Fail if found (means
   `HalCanary::hal_canary_init()` wasn't called pre-thread-spawn).
4. **Syscall cap-check coverage:** ensure every `Syscall::*` variant in
   `src/os/kernel/ipc/syscall.spl` is preceded by `_cap_check()`.
5. **W^X invariant:** scan `hal_paging_map` call sites for `W|X` flag combo.
   Fail if any (after parsing `flags: VmFlags`).

---

## 6. Multi-Arch Bootstrap Pipeline (AC-6)

### 6.1 `--arch=<triple>` dispatch in `bootstrap-from-scratch.sh`

Today the script accepts `--target=freebsd-x86_64` or `--target=simpleos-x86_64`
only. Extend to:

```
scripts/bootstrap/bootstrap-from-scratch.sh \
  --arch=<triple> --deploy
```

Triples (added):

| Triple | Codegen | Boot loader | QEMU machine | QEMU flags | Smoke output |
|---|---|---|---|---|---|
| `x86_64-unknown-simpleos-elf` | self-hosted | Limine | `q35` | `-cpu max -smp 1 -m 256M` | `[BOOT] SimpleOS x86_64 banner ... [SMOKE] ok` |
| `i686-unknown-simpleos-elf` | LLVM (no self-hosted isel) | Limine | `pc` | `-cpu pentium3 -smp 1 -m 256M` | `[BOOT] SimpleOS i686 banner ... [SMOKE] ok` |
| `aarch64-unknown-simpleos-elf` | self-hosted | U-Boot + DTB | `virt` | `-cpu cortex-a72 -smp 1 -m 512M -nographic -bios u-boot.bin` | `[BOOT] SimpleOS aarch64 ...` |
| `armv7-unknown-simpleos-elf` | LLVM | U-Boot + DTB | `virt` | `-cpu cortex-a15 -smp 1 -m 512M -nographic -bios u-boot.bin` | `[BOOT] SimpleOS armv7 ...` |
| `riscv64gc-unknown-simpleos-elf` | self-hosted | OpenSBI + DTB | `virt` | `-cpu rv64,smode=on -smp 1 -m 512M -bios opensbi-fw.bin` | `[BOOT] SimpleOS rv64gc ...` |
| `riscv32imac-unknown-simpleos-elf` | LLVM | OpenSBI + DTB | `virt` | `-cpu rv32,smode=on -smp 1 -m 256M -bios opensbi-rv32.bin` | `[BOOT] SimpleOS rv32imac ...` |

`bin/simple build`'s arch flag (`--arch=<name>`) **already exists**
(`src/app/cli/main.spl:138-173`). The bootstrap script wraps that.

### 6.2 Boot-loader artifacts location

```
build/freebsd/        # existing, unchanged
build/simpleos/x86_64/
build/simpleos/i686/
build/simpleos/aarch64/
build/simpleos/armv7/
build/simpleos/riscv64gc/
build/simpleos/riscv32imac/
    {kernel.elf, kernel.bin, image.iso|image.img, qemu.log, smoke.log}
```

### 6.3 CI matrix wiring

`bin/simple test --arch=<triple>` already exists. The new audit:
`bin/simple test --arch=all` iterates all six. Phase 7 (Verify) wires this
into the `test/os/port/e2e_qemu_smoke_spec.spl` parameterization.

---

## 7. NVFS 32-bit Layout Stability (R5)

### 7.1 Audit findings

`src/lib/nogc_sync_mut/fs/nvfs/superblock_if.spl` (21 LoC) declares:

```
class Superblock:
    magic: i64                 # already fixed-width 64-bit
    version_major: i32         # already fixed-width 32-bit
    version_minor: i32
```

`src/lib/nogc_sync_mut/fs/nvfs/extent_map.spl` (31 LoC) and `api.spl` (12 LoC)
similarly use fixed-width `i32`/`i64`. **The on-disk format is already
arch-neutral** (no `usize`/`uintptr_t` in superblock). The only 32-bit
foot-gun is in-memory pointers cast to `u64` for MDSOC port table entries —
which are runtime-only, not on-disk.

### 7.2 Recommendation: option (a) — keep on-disk format 64-bit-fixed

- **Keep on-disk format 64-bit-fixed** with no superblock change.
- 32-bit kernels truncate-on-load when the in-memory pointer width is 32-bit
  (return `Result.Err(NvfsError.PointerTooLarge)` if a high bit is set on a
  32-bit kernel; in practice this only happens on >4GiB-mapped extents,
  outside the smoke-test scope).
- Add a Phase 5 unit test: load a 64-bit-written volume on a 32-bit kernel
  and verify clean `Result.Err` for >4GiB extents, `Result.Ok` for sub-4GiB.
- **Rejected:** option (b) arch-tagged superblock — adds complexity, breaks
  cross-arch portability of NVFS volumes, no real benefit since the format
  is already fixed-width.

---

## 8. Module List (Phase 5 Implementation Order)

### 8.1 Wave 1 — HAL trait additions (serial, lands first)

| File | Action | Purpose |
|---|---|---|
| `src/os/kernel/arch/hal.spl` | MODIFY | Add traits §2.3.1–§2.3.8 (HalEntropy, HalCstart, HalSyscall, HalCanary, HalBarrier, HalCache, HalSmp-reserved, HalPerCpu-reserved) |
| `src/os/kernel/arch/arch_context.spl` | MODIFY | Add `JmpBuf` per-arch sizing |

### 8.2 Wave 2 — `arch/common/` shared helpers (serial, lands second)

| File | Action |
|---|---|
| `src/os/kernel/arch/common/console_framing.spl` | CREATE |
| `src/os/kernel/arch/common/paging_walker.spl` | CREATE |
| `src/os/kernel/arch/common/interrupt_dispatch.spl` | CREATE |
| `src/os/kernel/arch/common/timer_math.spl` | CREATE |
| `src/os/kernel/arch/common/context_layout.spl` | CREATE |
| `src/os/kernel/arch/common/sbi_shim.spl` | CREATE |
| `src/os/kernel/arch/common/gic_common.spl` | CREATE |
| `src/os/kernel/arch/common/x86_descriptor.spl` | CREATE |
| `src/os/kernel/arch/common/relocations.spl` | CREATE |

### 8.3 Wave 3 — Per-arch impl of new HAL traits (parallel, 6 agents, disjoint scope)

For each `<arch>` ∈ {x86_64, x86_32, arm64, arm32, riscv64, riscv32}:

| File | Action |
|---|---|
| `src/os/kernel/arch/<arch>/cstart.spl` | CREATE — HalCstart impl |
| `src/os/kernel/arch/<arch>/entropy.spl` | CREATE — HalEntropy impl |
| `src/os/kernel/arch/<arch>/syscall_entry.spl` | CREATE — HalSyscall impl |
| `src/os/kernel/arch/<arch>/canary.spl` | CREATE — HalCanary impl |
| `src/os/kernel/arch/<arch>/barrier.spl` | CREATE — HalBarrier impl |
| `src/os/kernel/arch/<arch>/cache.spl` | CREATE — HalCache impl |
| `src/os/kernel/arch/<arch>/paging.spl` | MODIFY — refactor to use `arch/common/paging_walker.spl`, target ≤270 LoC each |
| `src/os/kernel/arch/<arch>/console.spl` | MODIFY — use `arch/common/console_framing.spl` |
| `src/os/kernel/arch/<arch>/interrupt.spl` | MODIFY — use `arch/common/interrupt_dispatch.spl` |
| `src/os/kernel/arch/<arch>/timer.spl` | MODIFY — use `arch/common/timer_math.spl` |
| `src/os/kernel/arch/<arch>/context.spl` | MODIFY — use `arch/common/context_layout.spl` |

Disjoint per-arch scope means the 6 agents can run in parallel.

### 8.4 Wave 4 — C→Simple ports (parallel, 5 agents)

| File | Action |
|---|---|
| `src/os/runtime/baremetal/runtime_minimal.spl` | CREATE (port `runtime_minimal.c`) |
| `src/os/libc/simpleos_libc.spl` | CREATE (port `simpleos_libc.c`) |
| `src/os/libc/simpleos_fs.spl` | CREATE |
| `src/os/libc/simpleos_stdlib_ext.spl` | CREATE |
| `src/os/libc/simpleos_string_ext.spl` | CREATE |
| `src/os/libc/simpleos_time.spl` | CREATE |
| `src/os/libc/simpleos_alloc.spl` | CREATE |
| `src/os/libc/simpleos_pthread.spl` | CREATE |
| `src/os/libc/simpleos_process.spl` | CREATE |
| `src/os/libc/simpleos_cxxabi.spl` | CREATE — replace `__stack_chk_guard` with `HalCanary` |
| `src/os/libc/simpleos_signal.spl` | CREATE |
| (delete after port verified) | `src/os/libc/simpleos_*.c`, `simpleos_crt0.S`, `simpleos_setjmp.S`, `arm64/boot/crt0.S`, `runtime_minimal.c` |

### 8.5 Wave 5 — bootstrap + audit + smoke

| File | Action |
|---|---|
| `scripts/bootstrap/bootstrap-from-scratch.sh` | MODIFY — add `--arch=` 5 new lanes |
| `src/app/build/os_harden_audit.spl` | CREATE — §5.2 checks |
| `test/os/port/e2e_qemu_smoke_spec.spl` | MODIFY — parameterize over 6 archs |
| `test/os/kernel/arch/hal_x86_64_phase_a_spec.spl` | CREATE |
| `test/os/kernel/arch/hal_x86_32_phase_a_spec.spl` | CREATE |
| `test/os/kernel/arch/hal_arm32_phase_a_spec.spl` | CREATE |
| `test/os/kernel/arch/hal_riscv32_phase_a_spec.spl` | CREATE |
| `doc/04_architecture/mdsoc_architecture_tobe.md` | MODIFY — link to this doc |

---

## 9. Data Flow

### 9.1 Boot → kernel-init → smoke run

```
[bootloader]                                                   <-- Limine/U-Boot/OpenSBI
    │ hand off (BootInfo struct + DTB ptr | Limine MemMap)
    ▼
[arch/<arch>/boot.spl: _start]                                 <-- arch-specific entry
    │ stack setup, BSS clear, paging early-init
    │ → calls HalCstart::hal_cstart_init()                     <-- HAL boundary crossed (1)
    ▼
[arch/common/ + arch/hal.spl shared init]
    │ HalConsole::init  (HAL boundary 2)
    │ HalBoot::parse_boot_info() -> BootOutputPort
    │ HalPaging::init(boot_info)
    │ HalEntropy::random_seed_u64() → HalCanary::init()
    │ HalInterrupt::install_idt + HalSyscall::install_vector
    │ HalTimer::init
    ▼
[src/os/kernel/boot/kernel_entry.spl: kernel_main]             <-- arch-neutral
    │ services init: scheduler, vmm, ipc, vfs (NVFS mount)
    ▼
[smoke harness: test/os/smoke/*.spl]
    │ assertions via println → HalConsole::writeln
    │ exit via HalPower::system_reset(test_mode=true)
    ▼
[QEMU exits, test_runner_new asserts smoke.log]
```

The HAL boundary is crossed exactly once at each transition: arch-specific
`_start` → `HalCstart` → arch-neutral `kernel_main`. Arch-neutral code never
imports `os.kernel.arch.<arch>.*` directly (audit script enforces).

### 9.2 Syscall path

```
[user code]
    │ ecall / svc / syscall / int 0x80 (per arch)
    ▼
[arch/<arch>/syscall_entry.spl: HalSyscall::hal_syscall_install_vector hook]
    │ register save into arch-specific frame
    │ HalCanary check on kernel stack
    │ _cap_check(current_proc, syscall_nr)                     <-- single cap-check site
    ▼
[src/os/kernel/ipc/syscall.spl: dispatch table]                <-- arch-neutral
    ▼
[service handler]
    │ result → arch frame
    ▼
[arch/<arch>/syscall_entry.spl: return path]
    │ register restore + return-from-trap
    ▼
[user code resumes]
```

---

## 10. Integration Points

| Surface | Status | Action |
|---|---|---|
| `harden-nvfs-simpleos` sstack feature | Shipped 2026-04-24 | Reuse: typed `Result` errors, `MountOptions.want_caps/require_caps`, `audit_log.spl`, bounded I/O via bulk extern |
| `doc/04_architecture/mdsoc_architecture_tobe.md` | Existing | Add link to this doc + note HAL is the kernel's MDSOC outer-edge |
| `src/os/qemu_runner.spl` | Existing, multi-arch already | Add `riscv32` LLVM-fallback lane validation + `armv7` U-Boot setup |
| `bin/simple test --arch=<triple>` | **Already exists** in `src/app/cli/main.spl:138` — confirmed | No new flag needed; only Phase 5 wires `--arch=all` iterator |
| `bin/simple build --arch=` | Already exists | Same |

---

## 11. Open Questions for User (escalate before Phase 4)

1. **PAE on x86_32:** Do AC-4 smoke tests need hardware-W^X on x86_32, or is
   mapping-discipline (no `W|X` mapping ever) acceptable? Default plan:
   mapping-discipline for AC-4; PAE deferred. **Confirm.**
2. **HalSmp / HalPerCpu impl:** trait shape locked; impl deferred to a
   follow-up feature. UP-only kernel for AC-4. **Confirm.**
3. **HalFpContext:** not added this round. If userland SIMD/FPU is on the
   horizon, reserve `hal_context_save_extended()` on `HalContext` now to
   avoid ABI churn. **Confirm reserve-now or defer-trait-too.**
4. **40% LoC reduction feasibility:** **Achievable contingent on
   paging-walker extraction.** Phase 5 must validate by prototyping the
   walker on x86_64 first; if x86_64 paging shrinks from 531 → ≤270 LoC,
   the 40% target is on track. If walker extraction fails, ~25% is the
   realistic floor. **User pre-approval to fall back to ~25% if walker
   extraction blows scope?**
5. **AC-3 path divergence:** AC-3 wording specifies HAL boundary at
   `src/os/hal/<arch>/`. The existing HAL boundary is at
   `src/os/kernel/arch/<arch>/` and `src/os/kernel/arch/hal.spl` (per
   Phase 2 finding — boundary already exists with 6-arch dispatch). Plan
   **keeps existing path**. **Confirm AC-3 amendment to read
   `src/os/kernel/arch/<arch>/`, or relocate the entire `arch/` tree?**

---

## Appendix A — Per-arch file inventory at start of Phase 5

```
src/os/kernel/arch/
├── hal.spl                       (1,197 LoC — modify Wave 1)
├── arch_context.spl              (modify Wave 1)
├── mod.spl                       (206 LoC — unchanged)
├── arm/
│   └── pl011_common.spl          (extend Wave 2)
├── common/                       (NEW — Wave 2 creates)
│   ├── console_framing.spl
│   ├── paging_walker.spl
│   ├── interrupt_dispatch.spl
│   ├── timer_math.spl
│   ├── context_layout.spl
│   ├── sbi_shim.spl
│   ├── gic_common.spl
│   ├── x86_descriptor.spl
│   └── relocations.spl
├── x86_64/  (2,746 LoC — modify Wave 3 + add 6 new files)
├── x86_32/  (1,760 LoC — modify Wave 3 + add 6 new files)
├── arm64/   (1,801 LoC — modify Wave 3 + add 6 new files)
├── arm32/   (1,806 LoC — modify Wave 3 + add 6 new files)
├── riscv64/ (2,644 LoC — modify Wave 3 + add 6 new files)
└── riscv32/ (1,533 LoC — modify Wave 3 + add 6 new files)
```

---

## Appendix B — Codex cross-check summary (2026-04-25)

Codex review consulted on HAL surface gaps, x86_32 W^X, and stack-canary
entropy. Key adoptions:
- Added HalSmp, HalPerCpu (reserved-only), HalBarrier, HalCache traits.
- W^X on i686-non-PAE: mapping-discipline pattern, PAE-mandatory only if
  userspace exec is in scope.
- Entropy: `hal_random_seed_u64` is best-effort early seed, NOT crypto RNG;
  layered fallback per arch.
- HalFpContext deferred but reserved on `HalContext::context_save_extended`.

---

*End of architecture brief — Phase 3 (Architect) lock for
simpleos-multiarch-harden, 2026-04-25.*
