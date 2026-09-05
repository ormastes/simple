# Baremetal Skill - Index-Based Pointer & Allocator Discipline

Reference: `src/lib/nogc_async_mut_noalloc/` (baremetal/execution/memory tier),
`examples/09_embedded/simpleos_nvme_fw/` (NVMe firmware example).

## Core Rule

Baremetal/noalloc code never carries raw pointers or GC references across
state. It carries **integer indices into fixed-capacity arrays** (pools/
arenas), optionally paired with a **generation counter** to detect
use-after-free without a GC. No unbounded `.push()`/heap growth on hot or
interrupt paths.

## Owner Modules

| Module | Role |
|--------|------|
| `src/lib/nogc_async_mut_noalloc/baremetal/{arm,arm64,riscv,riscv32,x86,x86_64}/` | Arch-specific noalloc boot/runtime |
| `src/lib/nogc_async_mut_noalloc/baremetal/common/` | Shared noalloc harness (`test_harness.spl`, `mod.spl`) |
| `src/lib/nogc_async_mut_noalloc/execution/`, `memory/` | noalloc execution + memory primitives |
| `src/os/kernel/boot/riscv_noalloc_pmm.spl` | Scalar monotonic physical-page allocator (no arrays, no Option/Result) |
| `src/os/kernel/memory/pmm.spl`, `heap.spl` | Hosted PMM/heap — **above** the noalloc tier, real virtual addrs |
| `src/os/services/nvfs/core/arena.spl` | Index-keyed arena store pattern (`_find_index` over parallel arrays) |
| `examples/09_embedded/simpleos_nvme_fw/fw/fw_pool.spl` | 16-slot generation-handle task pool (`TaskPool`) |
| `examples/09_embedded/simpleos_nvme_fw/pool_demo.spl` | Canonical `Handle{index, generation}` reference impl |
| `examples/09_embedded/simpleos_nvme_fw/fw/ftl_map.spl`, `ftl_band.spl` | L2P map cache / band allocator, all `UNMAP`-sentinel index arrays |
| `src/os/drivers/nvme/nvme_queue.spl` | Real NVMe SQ/CQ ring — producer/consumer **indices** (`sq_tail`, `cq_head`), not pointers |

## Do

- Represent a "live object" as `Handle(index: i64, generation: i64)` into a
  parallel-array pool; bump the slot's generation on release so stale handles
  are rejected cheaply (no GC):

```simple
struct Handle:
    index:      i64
    generation: i64

me phase_of(h: Handle) -> i64:
    if me.gens[h.index] != h.generation or me.used[h.index] == 0:
        return UNMAP   # stale/free handle rejected
    me.t_phase[h.index]
```

- Fix pool/cache/arena capacity as a `val CAP: i64` constant and pre-fill all
  backing arrays at init time (`while i < CAP: arr.push(...)`) — growth
  happens once, at startup, never per-request.
- Use a sentinel (`UNMAP = -1`) for "no entry" instead of null/Option in
  index arrays — cheap, allocation-free, branch-friendly.
- Track queue/ring position as a wrapping index (`self.sq_tail = (self.sq_tail + 1) % self.depth`),
  never as a pointer that walks memory.
- Keep true MMIO/DMA addressing (`mmio_write32(doorbell, ...)`, ring entry at
  `sq_virt + tail * 64`) — this is unavoidable for real hardware register/ring
  access, but confine it to the driver's register/ring layer; business logic
  above it stays index-based (see `nvme_queue.spl` vs `fw_pool.spl`).
- Name any raw-address escape hatch explicitly (`unsafe_addr_of`) so it's
  greppable and reviewable, and keep it to a single narrow helper.

## Don't

- Don't store a live pointer/reference into a growable array element (it
  invalidates on reallocation) — store the index and re-index on every access.
- Don't call unbounded `.push()`/dynamic alloc on an interrupt handler or
  scheduler hot path — verified clean today: `src/os/kernel/interrupts/` and
  `examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_*.spl` (rv32 firmware
  target logic) have zero `.push()` calls.
- Don't reach for the hosted heap (`os.kernel.memory.heap.KernelHeap`,
  mimalloc-backed) from noalloc/early-boot/rv32-firmware code — that heap is
  a separate, higher tier with real virtual addresses and is not part of the
  noalloc discipline.
- Don't skip the generation check when consuming a `Handle` — an index alone
  cannot detect a released-and-reused slot.

## How NVMe FW Applies This

`examples/09_embedded/simpleos_nvme_fw/` is the concrete worked example:
- **Task pool**: `fw/fw_pool.spl` — 16-slot `TaskPool`, one row per in-flight
  NVMe command, addressed by `Handle{index, generation}` (`pool_demo.spl`).
- **FTL L2P cache**: `fw/ftl_map.spl` — fixed `MAP_CACHE_CAP`-slot cache over
  parallel `[i64]` arrays (`c_lba`, `c_ppn`, `c_dirty`, `c_age`), `UNMAP`
  sentinel for unmapped LBAs, LRU eviction by index (`ftl_lru_slot`).
  `fw/ftl_band.spl` allocates NAND bands the same way (`BandAlloc`).
  Recovery is log-structured (WAL replay), never pointer-based.
  All fixed-size, no growth after init.
- **Boot allocator**: `src/os/kernel/boot/riscv_noalloc_pmm.spl` hands out
  4 KiB physical pages monotonically from a scalar `u64` cursor — no arrays,
  no `Option`/`Result`, no text/logging allocation, so it's safe before any
  heap exists.
- **Real driver ring**: `src/os/drivers/nvme/nvme_queue.spl` — `sq_tail`/
  `cq_head` are wrapping `u16` producer/consumer indices into a fixed-depth
  ring; the only raw address arithmetic is the unavoidable MMIO/DMA byte
  offset (`sq_virt + tail_u64 * 64`) into hardware-defined ring memory.

## Audit Result (2026-07-11)

No violations found: rv32 firmware logic files (`fw_rv32/logic_*.spl`) and
`src/os/kernel/interrupts/` contain zero `.push()`/growable-alloc calls.
Raw-address use is confined to MMIO/DMA register and ring-entry addressing
(`nvme_queue.spl`, `_NvmeDriver/dma_addrs.spl`'s `unsafe_addr_of`), which is
expected — real NVMe hardware rings are byte-addressed and cannot be made
purely index-into-array. Everything above that layer (task pool, L2P map,
band allocator, boot PMM) is index/generation-handle based.

## See Also

- `doc/05_design/os/nvfs/nvfs_design.md` §4.1/§12 — arena primitive design
- `doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md`
- `doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md`
- `.claude/rules/bootstrap.md` — pure-Simple self-hosted build discipline
