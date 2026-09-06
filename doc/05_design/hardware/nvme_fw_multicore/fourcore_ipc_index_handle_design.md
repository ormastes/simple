# Four-Core rv32 NVMe FW: Index-Handle IPC Design (v1)

Status: design contract for the 2026-07-19 wave-3 campaign.
Goal (user directive): index-based pointers + allocator instead of raw pointers,
intensively; 4-core rv32 partition (HIL / FTL / FIL / NAND-emu, one per core);
queue-based IPC + other IPC between cores; harden fw + rv32 Simple code.

## 1. Ground truth (surveyed 2026-07-19)

- `fw/` is already index-based end-to-end: `Handle{pool,index,generation}`
  (`nvme_types.spl:11`), `TaskPool` generation-handle pool (`fw_pool.spl`),
  `DramSpan` fixed arena (`dram.spl`), `alloc_spare` (`fil_badblock.spl:52`),
  ppn/lba + `nd_types` typed dims. No pointer arithmetic, no real DMA (PRPs are
  simulated i64 tags). The wave-3 pointer work is therefore: (a) codify the law,
  (b) name the sentinels, (c) make ALL new multicore IPC index-only.
- `fw_rv32/` is a single-hart scalar monolith (`logic_*` domains, no arrays/heap;
  `entry.spl` + hand-written `_start` asm in `build.shs`; QEMU `-machine virt`,
  no `-smp`). SMP precedent exists only in the OS path
  (`src/os/kernel/arch/riscv32/boot.spl`: `amoadd.w` census + mhartid gate) and
  CLINT scaffolding (`nogc_async_mut_noalloc/baremetal/riscv/clint.spl`, MMIO
  bodies commented out).
- No SPSC/MPSC ring exists in the repo. `fw/hil_queue.spl` (SQ/CQ split ring)
  and `collections/ring_buffer.spl` (mask math) are single-threaded templates.
- Baremetal `volatile_ops`/`memory_barrier` are LINKER STUBS (no-ops) on
  freestanding rv32 — never rely on them. Reliable primitives: naturally-aligned
  32-bit loads/stores (atomic on rv32) + `fence` via the asm stub. A-extension
  is enabled (`+m,+a,+c`) but v1 SPSC needs no AMO.

## 2. The index-base-pointer law (applies to ALL wave-3 code)

1. No raw addresses in Simple firmware code. Every cross-module / cross-core
   reference is a TYPED INDEX into a named, fixed-capacity region or pool.
2. Address math (base + idx*4) exists ONLY in the asm-stub externs (rv32) or the
   host-check shm array accessor (host). One boundary, auditable.
3. Null sentinel is a NAMED constant (`IPC_NULL_IDX = -1`), never a bare -1.
4. Every index is bounds-checked FAIL-CLOSED at the pool/region boundary before
   use; violations increment an error word and abort the operation (never wrap,
   never clamp-and-continue).
5. Messages crossing cores carry only: opcodes, status codes, typed indices,
   small scalars. Never arrays-by-value, never addresses.
6. Buffers are allocated from the index pool by the producer, freed by the final
   consumer; the buffer INDEX travels in the message (this is the "allocator
   instead of raw pointer" requirement made concrete).

## 3. Shared-memory region map (word-indexed, 4-byte slots)

One linker-reserved NOLOAD region `_ipc_shm` (rv32) / one `[i64]` array (host
checks). All constants live in `fw_rv32/logic_ipc_layout_core.spl` (pure, shared
by all lanes; host checks import the same file — single source of truth).

| Name | Word index | Size (words) | Owner (writer) |
|---|---|---|---|
| `IPC_GATE` | 0 | 1 | hart0 (write-once magic `0x4E564D45`) |
| `IPC_CENSUS` | 1 | 1 | all harts (amoadd in asm stub) |
| `IPC_ERR_COUNT` | 2 | 1 | any (diagnostic, monotonic) |
| reserved | 3 | 1 | — |
| rings ×6 | 4 .. 219 | 36 each | see §4 |
| buf pool | 220 .. 253 | 34 | HIL allocs, NAND-side path frees per §5 |
| NAND state | 256 .. 4351 | 4096 | core3 only |
| NAND data | 4352 .. 8447 | 4096 | core3 only |

Total `IPC_SHM_WORDS = 8448` (33 KB). NAND geometry reuses the drift-guarded
constants: `NUM_BLOCKS=64`, `PAGES_PER_BLOCK=64`, `NUM_PAGES=4096`; page data is
a single-word payload stand-in, matching `fw/` convention.

## 4. Queue-based IPC: SPSC rings

Six rings, ids 0..5: `R_HIL2FTL=0, R_FTL2HIL=1, R_FTL2FIL=2, R_FIL2FTL=3,
R_FIL2NAND=4, R_NAND2FIL=5`. `ring_base(r) = 4 + r*RING_WORDS`.

- `RING_DEPTH = 8` (power of two), `MSG_WORDS = 4`,
  `RING_HDR_WORDS = 4` (`+0 HEAD` consumer-owned, `+1 TAIL` producer-owned,
  `+2 DROP_COUNT` producer-owned, `+3` reserved), `RING_WORDS = 36`.
- Head/tail are free-running counters; slot = `counter & (RING_DEPTH-1)`;
  full = `tail - head == RING_DEPTH`; empty = `tail == head`.
- SPSC invariant: exactly one producer hart writes TAIL, exactly one consumer
  hart writes HEAD. Publish order: write payload words → `fence` → write TAIL.
  Consume order: read TAIL → `fence` → read payload → write HEAD.
- All ring algebra is PURE functions in `logic_ipc_ring_core.spl` taking
  (head, tail, depth, ...) scalars and returning packed verdicts; the thin
  drivers perform the shm loads/stores the verdict prescribes.

Message format (4 words): `w0 = opcode | (tag<<8) | (status<<16)`,
`w1 = lba_or_ppn`, `w2 = buf_idx` (index into buf pool — NEVER data, NEVER an
address), `w3 = aux` (block index for erase, error detail). Opcodes:
HIL→FTL `OP_WRITE=1, OP_READ=2, OP_FLUSH=3`; FTL→FIL `OP_PROG=4, OP_RD=5,
OP_ERASE=6`; FIL→NAND `NOP_PROG=7, NOP_READ=8, NOP_ERASE=9`. Status:
`ST_OK=0, ST_ERR=1, ST_MEDIA=2, ST_BOUNDS=3`. Codec is pure
(`logic_ipc_msg_core.spl`), round-trip checked.

## 5. Index pool allocator (buf pool)

`logic_buf_pool_core.spl` — fixed 16-slot pool, O(1) alloc/free via intrusive
free-list stored in the pool's NEXT words. Header: `FREE_HEAD (+0)`,
`ALLOC_COUNT (+1)`; `NEXT[16] (+2..+17)`; `DATA[16] (+18..+33)`.

- `alloc`: pop FREE_HEAD; empty pool → `IPC_NULL_IDX` verdict (caller backoffs).
- `free(idx)`: bounds-check, double-free guard (NEXT[idx] must be the
  `BUF_IN_USE = -2` marker while allocated), push to FREE_HEAD.
- v1 ownership discipline avoids cross-core races on the pool: HIL (hart0)
  allocates AND frees; frees happen at completion-reap time (single writer for
  header words). Data words are written by whichever core the message grants
  the buffer to (exclusive by protocol while in-flight).
- Pure core returns (verdict, new_head, new_count, slot_to_touch) packed; the
  driver executes the 2–3 prescribed shm ops.

## 6. Four-core partition + boot protocol (rv32)

- `mhartid` dispatch: hart0=HIL, hart1=FTL, hart2=FIL, hart3=NAND-emu.
- Boot: `_start` (asm, build.shs) sets per-hart stack (4 stacks; nogc startup
  already sizes 4×64K — the fw stub reserves its own 4×16K in .bss), bumps
  `IPC_CENSUS` via `amoadd.w`, hart0 → `rt_rv32_fourcore_main(0)`, harts 1–3
  spin on `IPC_GATE` (fence-load loop with `wfi` between polls) then call
  `rt_rv32_fourcore_main(hartid)`.
- hart0: zero shm, init NAND state (all erased), init buf-pool free-list, run
  the existing single-hart `nvme_fw_rv32_selftest` first (regression guard),
  write `IPC_GATE = GATE_MAGIC`, send IPI to harts 1–3 (CLINT MSIP — the "other
  IPC"), then enter the HIL loop.
- "Other IPC" mechanisms (non-queue): (a) IPC_GATE start-gate word,
  (b) CLINT MSIP doorbell IPI on enqueue → consumer `wfi` wake + `ipi_clear`,
  (c) census word. Rings remain correct without IPIs (polling); IPIs are a
  wakeup optimization and are themselves verified by the boot transcript.
- Every wait loop has a spin budget (`SPIN_MAX`); exhaustion prints a FAIL
  marker and parks — fail-closed, no silent hangs.

## 7. Extern surface (implemented in the build.shs asm stub)

`rt_rv32_shm_load(idx)->i64`, `rt_rv32_shm_store(idx,val)`, `rt_rv32_fence()`,
`rt_rv32_hartid()->i64`, `rt_rv32_ipi_send(hart)`, `rt_rv32_ipi_clear()`,
`rt_rv32_wfi()`, existing `rt_riscv_uart_put(byte)`. The asm bodies are the ONLY
place `_ipc_shm` base address, `CLINT_BASE (0x02000000)` and MSIP offsets
appear. Simple-side declarations live in one file (`entry_smp.spl`).

## 8. Dataplane selftest (the e2e oracle)

HIL writes 3 LBAs (distinct data words), flushes, reads back, verifies values,
then exercises: bounds-violation command (expects ST_BOUNDS), pool-exhaustion
backoff (alloc 17th buf → NULL_IDX path), and a full-ring backpressure case.
Each stage prints a marker; final marker `ALL RV32 4CORE IPC CHECKS PASS`.
The SAME state machines run host-side in `ipc_fourcore_check.spl` (host-only
`[i64]` shm + round-robin scheduler calling each core's step fn) — logic
identical, only the shm accessor differs.

## 9. Build/boot integration

- `build.shs`: `NVME_RV32_SMP=1` selects the SMP stub (per-hart stacks, census,
  gate park, fourcore entry) + links `entry_smp.spl` instead of the single-hart
  path. Default (unset) build is UNCHANGED (regression safety).
- `boot.shs`: `--smp` flag adds `-smp 4` and expects the 4CORE marker;
  default run unchanged, still expects `ALL RV32 NVME FW CHECKS PASS`.
- Linker: `.ipc_shm (NOLOAD)` section, `_ipc_shm` symbol, 33 KB, after .bss.

## 10. Lane table

| Lane | Deliverable | Model | Depends |
|---|---|---|---|
| L1 | fw/ index-law audit: named sentinels (`NULL_IDX` etc.) replacing bare -1 null-handles, law section in PRODUCTION_STATUS; NO behavior change | sonnet | — |
| L2 | `logic_ipc_layout_core.spl` + `logic_ipc_ring_core.spl` + checks | sonnet | — |
| L3 | `logic_ipc_msg_core.spl` codec + check | haiku | — |
| L4 | `logic_buf_pool_core.spl` + `logic_nand_region_core.spl` + checks | sonnet | — |
| L5 | `logic_fourcore_core.spl` (4 step machines) + `ipc_fourcore_check.spl` host e2e harness | opus | L2,L3,L4 |
| L6 | `entry_smp.spl` + build.shs/boot.shs SMP stub + linker + QEMU 4-core boot gate | opus | L5 |
| L7 | const_drift_check extension (ring/pool/layout constants), hardening audit, docs/wiki refresh | sonnet | L5,L6 |

Verification matrix: every `*_check.spl` is a host-runnable plain program
(rc meaningful, per fw convention) with absolute oracles + at least one
deliberate-red calibration during development; L6 additionally requires a real
QEMU `-smp 4` transcript with the final marker; L7 re-runs the single-hart boot
gate to prove no regression.
