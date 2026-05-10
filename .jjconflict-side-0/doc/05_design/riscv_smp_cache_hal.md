# RISC-V SMP + Cache HAL Design

**Feature:** `riscv_smp_cache_hal_phase1`
**Date:** 2026-05-02
**Phase:** 3-arch
**State file:** `.sstack/riscv_smp_cache_hal_phase1/state.md`

---

## 1. Overview

Implements `HalSmp` and `HalCache` traits for RISC-V 64-bit and 32-bit targets.
These traits were reserved ("impl deferred") in `doc/04_architecture/simpleos_multiarch_hal.md`
§2.3.5 (HalSmp) and §2.3.8 (HalCache). This design fills the implementation gap.

Architecture style: **MDSOC-only** (kernel/drivers; no ECS business layer per CLAUDE.md).

---

## 2. New and Modified Files

| File | Role | New/Modified |
|------|------|--------------|
| `src/os/kernel/arch/riscv64/sbi.spl` | SBI IPI ext v0.3 + legacy + probe ladder | Modified |
| `src/os/kernel/arch/riscv32/sbi.spl` | rv32 mirror of SBI additions | Modified |
| `src/os/kernel/arch/riscv64/dtb_scan.spl` | Scoped FDT /cpus walker; memoized boot-time results | New |
| `src/os/kernel/arch/riscv32/dtb_scan.spl` | rv32 mirror (u32 pointers) | New |
| `src/os/kernel/arch/riscv64/smp.spl` | `HalSmp` impl for rv64 | New |
| `src/os/kernel/arch/riscv32/smp.spl` | `HalSmp` impl for rv32 (u64→u32 truncation explicit) | New |
| `src/os/kernel/arch/riscv64/cache.spl` | `HalCache` impl for rv64; Zicbom CMO + fence.i fallback | New |
| `src/os/kernel/arch/riscv32/cache.spl` | `HalCache` impl for rv32 | New |
| `src/os/kernel/arch/riscv64/mod.spl` | Re-export smp, cache, dtb_scan | Modified |
| `src/os/kernel/arch/riscv32/mod.spl` | Re-export smp, cache, dtb_scan | Modified |
| `src/lib/nogc_async_mut_noalloc/baremetal/riscv/startup.spl` | `tp` write + AP spin-and-start protocol | Modified |
| `src/lib/nogc_async_mut_noalloc/baremetal/riscv32/startup.spl` | Same for rv32 | Modified |
| `doc/04_architecture/simpleos_multiarch_hal.md` | Flip RESERVED → DONE for HalSmp + HalCache | Modified |

No writes to `arch/riscv/` (common) or `arch/common/` — per-arch duplication is intentional
to stay within scope and avoid touching shared modules.

---

## 3. Module Dependencies (no cycles)

```
boot.spl
  → dtb_scan_init(fdt_ptr)   [parse once, memoize]
  → hal_smp_init(fdt_ptr)    → dtb_scan (read-only after init)
                              → sbi.spl  (SBI ecalls)
                              → cpu.spl  (mhartid, read_tp)
  → hal_cache_init()         → dtb_scan (read-only after init)
                              → cpu.spl  (fence.i, CMO asm)

smp.spl  → sbi.spl
smp.spl  → cpu.spl
cache.spl → cpu.spl
dtb_scan.spl  [no deps — pure byte-walker]
```

---

## 4. DTB Scanner (`dtb_scan.spl`)

**Shape:** Scoped `/cpus` walker — NOT a full FDT parser.

**Minimum parsing contract:**
- Check `fdt_ptr != 0` and FDT magic `0xD00DFEED`.
- Walk struct-block tokens: `FDT_BEGIN_NODE (1)`, `FDT_PROP (3)`, `FDT_END_NODE (2)`.
- Properties read: `reg`, `status`, `riscv,isa`, `riscv,cbom-block-size`.
- Stop walking after exiting `/cpus` subtree — no need to parse full DTB.

**Public API:**
```
fn dtb_scan_init(fdt_ptr: u64)
fn cached_cpu_count() -> u32          # fallback: 1
fn cached_cbom_block_size() -> u32    # fallback: 64
fn cached_isa_string(hart_idx: u32) -> text
```

**Memoization:** `dtb_scan_init` is idempotent — second call with same pointer is a no-op.

**Hart enumeration algorithm:**
1. Validate FDT magic; on fail, set `cpu_count = 1` and return.
2. Walk struct block. On `cpu@N` child of `/cpus/`: increment candidate count.
3. Filter: `status = "disabled"` → exclude. `status` absent → include.
4. Read `reg` → store hartid in `hart_id_map[0..MAX_HARTS]`.
5. From first cpu node: read `riscv,cbom-block-size` and `riscv,isa`.
6. Cache all results.

---

## 5. SBI Shim Extensions (`sbi.spl` additions)

```
fn sbi_send_ipi_v3(hart_mask: u64, hart_mask_base: u64) -> SbiResult
    # EID = 0x735049, FID = 0  (SBI v0.3 IPI extension)

fn sbi_send_ipi_legacy(hart_mask_ptr: u64) -> SbiResult
    # EID = 0x04, FID = 0  (legacy M-mode deprecated)

fn sbi_probe_then_send_ipi(hart_mask: u64, hart_mask_base: u64)
    # Uses cached IPI_PATH (set once by hal_smp_init):
    #   IPI_PATH_V3     → sbi_send_ipi_v3
    #   IPI_PATH_LEGACY → sbi_send_ipi_legacy (hart_mask on stack)
    #   IPI_PATH_CLINT  → MMIO write 0x0200_0000 + 4*hartid = 1u32
```

**Boot-time probe ladder (called once from `hal_smp_init`):**
1. `sbi_probe_extension(0x735049)` ≥ 0 → `IPI_PATH_V3`
2. else `sbi_probe_extension(0x04)` ≥ 0 → `IPI_PATH_LEGACY`
3. else → `IPI_PATH_CLINT`

Result cached as enum in HalSmp capsule state. No re-probe on hot path.

---

## 6. HalSmp Impl

**rv64:** `impl HalSmp for RiscvSmp` in `riscv64/smp.spl`
**rv32:** `impl HalSmp for RiscvSmp32` in `riscv32/smp.spl`

**Capsule state:**
```
struct RiscvSmpState:
    cpu_count: u32
    ipi_path: IpiPath          # enum: V3 | Legacy | Clint
    hart_id_map: [u32; 64]     # DTB-discovered hartids
```

**Method implementations:**

`hal_smp_cpu_count() -> u32`
- Returns `RiscvSmpState.cpu_count` (set once by `hal_smp_init`).

`hal_smp_cpu_start(ap_id: u32, entry: u64, stack: u64, arg: u64) -> bool`
- SBI `sbi_hart_start` passes only one opaque register to the AP. Pack `stack` and `arg` into a
  static `AP_BOOT_ARGS: [ApBootArgs; MAX_HARTS]` array (in kernel BSS), set slot `ap_id`, then
  call `sbi_hart_start(ap_id as u64, entry, &AP_BOOT_ARGS[ap_id] as u64)`. The AP entry stub
  reads `stack` from `0(a1)` and `arg` from `8(a1)`, sets sp, and jumps to the kernel.
- rv32: casts `entry as u32`, `stack as u32`, `arg as u32` — explicit, documented.
- Returns true on `SBI_SUCCESS`.

`hal_smp_ipi_send(target: u32, vector: u32)`
- Writes `vector` into `PENDING_IPI[target]` (module-level `[u32; MAX_HARTS]` array, NOT
  `read_tp() + offset` — `read_tp()` returns the sender's base, not the target's).
- Calls `sbi_probe_then_send_ipi(1u64 << target, 0u64)`.

`hal_smp_ipi_broadcast(vector: u32)`
- Builds hart mask for all enabled harts except self.
- If `cpu_count <= 64`: one `sbi_probe_then_send_ipi` call with full bitmask.
- If `cpu_count > 64`: loop of individual calls (documented limitation).

---

## 7. HalCache Impl

**rv64:** `impl HalCache for RiscvCache` in `riscv64/cache.spl`
**rv32:** `impl HalCache for RiscvCache32` in `riscv32/cache.spl`

**Capsule state:**
```
struct RiscvCacheState:
    cbom_block_size: u32
    cmo_caps: RiscvCmoCaps

struct RiscvCmoCaps:
    has_zicbom: bool
    has_zicboz: bool
    has_zicbop: bool
```

**Canonical trait method names** (from `simpleos_multiarch_hal.md` §2.3.8):
- `hal_cache_sync_icache(addr: u64, len: u64)`
- `hal_cache_clean_dcache(addr: u64, len: u64)`
- `hal_cache_invalidate_dcache(addr: u64, len: u64)`

Note: AC-2 in the state file uses informal names (`dcache_clean`, `icache_invalidate`) — these
are incorrect shorthand. All specs and impls use the canonical names above.

**Method implementations:**

`hal_cache_sync_icache(addr, len)`
- Always emits `fence.i` (`0x0000100F`).
- If `has_zicbom`: additionally emits `cbo.flush` per cacheline over `[addr, addr+len)`.
- Cacheline stride: `cached_cbom_block_size()` (default 64).

`hal_cache_clean_dcache(addr, len)`
- If `has_zicbom`: emit `cbo.clean` per cacheline.
- Else: NO-OP + diagnostic log ("platform must be coherent").

`hal_cache_invalidate_dcache(addr, len)`
- If `has_zicbom`: emit `cbo.inval` per cacheline.
- Else if flush-only path: emit `cbo.flush` (clean+invalidate, safe upper bound).
- Else: NO-OP + diagnostic log.

---

## 8. CMO Probing

**Method 1 (primary):** Parse `riscv,isa` string from DTB (via `dtb_scan::cached_isa_string(0)`).
- Check for substrings: `_zicbom`, `_zicboz`, `_zicbop`.
- Per RISC-V ISA string convention (unpriv spec §27): multi-letter extensions follow base ISA,
  separated by `_`. Example: `rv64gc_zicbom_zicboz`.

**Method 2 (fallback):** Illegal-instruction trap probe (only if DTB silent).
- Install temporary trap handler catching `scause = 2` (illegal instruction), setting a flag.
- Execute one `cbo.inval a0` instruction. If trap fires → `has_zicbom = false`.
- Repeat for `cbo.zero` (Zicboz) and `prefetch.i` (Zicbop).
- Restore original trap vector after probe.

**Feature A handshake:**
- Per contract, Feature A Phase 3 extends `PortableNumericCapabilities` with
  `has_riscv_zicbom`, `has_riscv_zicboz`, `has_riscv_zicbop`, `requires_runtime_cache_probe`.
  Feature B writes directly into those fields — no parallel registry.
- `hal_cache_init()` writes probe results directly:
  ```
  capabilities.has_riscv_zicbom = probed_zicbom
  capabilities.has_riscv_zicboz = probed_zicboz
  capabilities.has_riscv_zicbop = probed_zicbop
  capabilities.requires_runtime_cache_probe = ...
  ```
- `RiscvCmoCaps` (local to `cache.spl`) is a probe-accumulator only — NOT a public struct
  or parallel registry. It is collapsed into the direct field write before PR.
- AC-3 satisfied when Feature A Phase 3 (fields) + Feature B Phase 5 (write) both land.

---

## 9. `tp` Per-CPU Base Register

**Write point:** `start.S` (baremetal entry), after sp setup, before `__spl_start_bare`:
```asm
csrr  t0, mhartid
la    t1, __per_cpu_data_base
slli  t0, t0, PER_CPU_SHIFT
add   tp, t1, t0
```
Secondary harts: same sequence in AP trampoline (added to `startup.spl`).

**Guard:** Only in baremetal builds (`riscv64gc-unknown-simpleos-elf` / `riscv32imac-unknown-simpleos-elf`).
Linux-hosted guest mode must NOT write `tp` (Linux TLS lives there).

**Trap frame:** `x4 = tp` must be explicitly saved/restored in the trap frame alongside x3 (gp).
The existing trap frame save block covers `x3-x31`; the implementation must confirm `x4` is
present at the correct register slot in `TrapFrame`.

---

## 10. Phase 5 Sub-Agent Plan

| Agent | Files (disjoint) | Dependency |
|-------|-----------------|------------|
| SA-1 | `riscv64/sbi.spl`, `riscv32/sbi.spl` | None — runs first |
| SA-2 | `riscv64/smp.spl`, `riscv32/smp.spl`, `riscv64/dtb_scan.spl`, `riscv32/dtb_scan.spl`, `baremetal/riscv/startup.spl`, `baremetal/riscv32/startup.spl`, `riscv64/mod.spl`, `riscv32/mod.spl` | SA-1 must land first |
| SA-3 | `riscv64/cache.spl`, `riscv32/cache.spl` | None — parallel with SA-2 |
| SA-4 | `test/os/kernel/arch/hal_riscv64_smp_cache_spec.spl`, `test/os/kernel/arch/hal_riscv32_smp_cache_spec.spl` | Parallel; uses stub impls |

**Execution order:** SA-1 → (SA-2 + SA-3 + SA-4 in parallel).

---

## 11. Risk Mitigations

| Risk | Mitigation |
|------|-----------|
| R1: SBI IPI ext absent | Boot-time probe ladder; `IPI_PATH_CLINT` MMIO fallback at `0x0200_0000 + 4*hartid` |
| R2: Zicbom illegal-instruction trap | DTB check first (no CMO exec); trap-guarded probe only if DTB silent |
| R3: DTB null / bad magic | Fallback: `cpu_count=1`, `cbom_block_size=64`, `has_zicbom=false` |
| R4: `tp` TLS clobber on Linux guest | `cfg(baremetal)` guard on `tp` write; verified by linker `.tbss`/`.tdata` absence check (Phase 6) |
| R5: rv32 u64→u32 pointer truncation | Explicit `as u32` casts in rv32 `HalSmp` impl; documented as precondition |

---

## 12. Acceptance Criteria Coverage

| AC | Module |
|----|--------|
| AC-1 | `smp.spl` (rv64+rv32) + `sbi.spl` additions |
| AC-2 | `cache.spl` (rv64+rv32); canonical `hal_cache_*` names used |
| AC-3 | `RiscvCmoCaps` shim in `cache.spl`; wire-up to Feature A on its Phase 5 |
| AC-4 | `startup.spl` `tp` write + trap frame `x4` save |
| AC-5 | SA-4 spec files (4 scenarios: DTB hart-count, IPI delivery, fence.i ordering, Zicbom avail-vs-fallback) |
| AC-6 | `startup.spl` change additive; GHDL acceptance scripts not touched |
| AC-7 | `simpleos_multiarch_hal.md` RESERVED → DONE flip + cross-links |
