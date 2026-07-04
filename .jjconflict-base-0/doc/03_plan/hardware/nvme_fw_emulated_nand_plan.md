# Plan: Working with Emulated NAND — an ONFI-style controller seam for the firmware

> **Status (2026-06-29): phase E3 IMPLEMENTED.** The ONFI NAND *device* + FIL-driving-it is
> built and run-green: `fw/fil_nand_device.spl` is a protocol-accurate ONFI device (CMD/ADDR/
> DATA latch + `exec()` state machine, STATUS reg, OOB, fault injection) and `fil.spl` composes
> it as a faithful drop-in for `fil_nand.Nand`, so every write/read/GC-erase/recovery in
> `sim_main`/`nvme_main` goes through the real ONFI handshake (300 self-test asserts green).
> **However it landed as a SINGLE module (`fil_nand_device.spl`), not the planned 4-module
> `nand_device`/`nand_bus`/`nand_bus_sw`/`nand_ctrl` split** — the register-seam decomposition,
> async busy-timing reactor (E4: R/B# polling + per-command deadlines), no-alloc rv32 boot (E5),
> and `nand_bus_mmio` (E6) are **still future**. Operator guide:
> `doc/07_guide/hardware/nvme_firmware/`. NOTE: §7 below claims a
> `examples/09_embedded/simpleos_nvme_fw/baremetal_rv32/` directory exists and proves the seam on
> rv32 — that directory **does not exist** and the Simple firmware was **not** booted on rv32
> (only a separate self-contained C NAND/FTL demo booted on `qemu-system-riscv32` as a toolchain
> proof). See the corrected note in §7.

> **Scope.** Evolve the SimpleOS NVMe firmware (`examples/09_embedded/simpleos_nvme_fw/fw/`)
> from an in-process array NAND (`fil_nand`, which the FIL reads/writes directly) into a proper
> **emulated NAND *device*** accessed through a **controller register interface**, so the FIL
> becomes a real *driver*. This makes the firmware production-shaped, exercises the
> "fully coroutine / asynchronous media" requirement with real busy-timing, and lets the *same*
> firmware run against (a) a host software model, (b) a bare-metal rv32 build on
> `qemu-system-riscv32`, and (c) — later — a real or QEMU hardware NAND controller.

<!-- sdn-diagram:id=emu_nand_seam -->
```
   FTL (unchanged: ftl.write/read/trim/gc/recover)
        │  page-level program/read/erase
        ▼
   FIL driver (fil.spl, rewritten)  ──issues ONFI command sequences──►
        │
        ▼
   NandBus  (the controller-register SEAM:  cmd/addr/data/status + R/B + DMA + ECC)
     ├── nand_bus_sw   → in-process NandDevice model        (host + bare-metal rv32)
     └── nand_bus_mmio → load/store to a controller base    (real HW / QEMU device — future)
        │
        ▼
   NandDevice  (the emulated "chip": media + ONFI state machine + busy timing + fault injection)
```

The seam is where "the chip" ends and "the firmware" begins. Today that boundary is a struct
field; this plan turns it into an ONFI-style register protocol — the same boundary a real
controller exposes.

---

## 1. Why a device/bus/driver split (vs. today's direct model)

| Today (`fil_nand`) | With the seam |
|--------------------|---------------|
| FIL calls `nand.program(ppn,…)` directly on an in-process struct | FIL issues ONFI command sequences (`CMD 80h → ADDR → DATA → CMD 10h → poll STATUS`) over `NandBus` |
| Media ops are synchronous and instant | Ops are asynchronous: command → BUSY (tR/tPROG/tBERS) → R/B# → completion; the reactor polls |
| No hardware-portable boundary | The register interface maps 1:1 to a real controller; swap `nand_bus_sw`→`nand_bus_mmio` |
| ECC/DMA done inline in `fil` | ECC + DMA are *controller* features (offload), driver reads `ECC_STATUS` |

This directly serves research requirements: **#1 coroutine** (real media latency to yield on),
**#5 offloadable** (DMA/ECC are controller ops), and the **MDSOC+ media domain** boundary.

---

## 2. Emulated NAND device model — `nand_device.spl`

The "silicon": media storage + an ONFI command/state machine + timing + fault injection.

**Geometry** (reuse `nvme_types`): NUM_PLANES=4 · BLOCKS_PER_PLANE=16 · PAGES_PER_BLOCK=64 ·
page = data + spare(OOB). Per page: `data`, `oob_lba`, `oob_seq`, `ecc`, `written` flag,
injected-bit-errors. Per block: lifecycle (FREE/OPEN/CLOSED/BAD), erase count (endurance),
read-disturb counter, factory-bad marker.

**ONFI command state machine** (simplified but realistic):

| Cmd code | Operation | Sequence |
|----------|-----------|----------|
| `00h`/`30h` | READ | `00h → 5×ADDR → 30h` → BUSY(tR) → R/B → page in DATA register |
| `80h`/`10h` | PROGRAM | `80h → 5×ADDR → DATA(in) → 10h` → BUSY(tPROG) → STATUS(FAIL bit) |
| `60h`/`D0h` | BLOCK ERASE | `60h → 3×ADDR(row) → D0h` → BUSY(tBERS) → STATUS(FAIL bit) |
| `70h` | READ STATUS | returns STATUS register immediately |
| `FFh` | RESET | aborts current op, clears registers |
| `90h` | READ ID | returns a synthetic device ID into DATA |
| `ECh` | READ PARAMETER PAGE | returns geometry (so the driver can self-configure) |

**STATUS register bits**: `RDY`(bit6, device ready), `ARDY`(bit5, array ready), `FAIL`(bit0,
last program/erase failed), `WP_N`(bit7). **R/B# pin**: low while BUSY.

**Fault / endurance injection** (the value of an *emulated* NAND): factory bad blocks; runtime
program-fail / erase-fail (one-shot or sticky); read bit-flips (0/1/≥2 → ECC OK/FIXED/FAIL);
read-disturb accrual; endurance cap (block wears out after N P/E → erases start failing); and
**power-fail**: inject a crash at any ONFI step — partial-program (page half-written), shorn
write, erase-interrupted — to drive recovery tests.

---

## 3. Controller register interface — `nand_ctrl.spl` + the `NandBus` seam

**Register map** (byte offsets from a controller base; 32-bit registers):

| Off | Reg | R/W | Meaning |
|-----|-----|-----|---------|
| 0x00 | `CMD` | W | write an ONFI command code |
| 0x04 | `ADDR` | W | push one address cycle (col/row); auto-sequences |
| 0x08 | `DATA` | R/W | page-buffer data port (or use DMA) |
| 0x0C | `STATUS` | R | device STATUS register (RDY/ARDY/FAIL) |
| 0x10 | `RB` | R | 1 = ready, 0 = busy (R/B# pin) |
| 0x14 | `ECC_STATUS` | R | NAND_OK / NAND_ECC_FIXED / NAND_ECC_FAIL for the last read |
| 0x18 | `DMA_ADDR` | W | host buffer address for a page transfer |
| 0x1C | `DMA_LEN` | W | transfer length |
| 0x20 | `DMA_CTRL` | W | 1=start dir-in (read), 2=start dir-out (program); reads as done flag |
| 0x24 | `IRQ_STATUS` | R/W1C | op-complete / error interrupt (for the reactor) |

**`NandBus` seam** — the only thing FIL talks to:
```
trait NandBus:
    me reg_write(off: i64, val: i64)
    me reg_read(off: i64) -> i64
    me buf_write(idx: i64, val: i64)   # page-buffer staging
    me buf_read(idx: i64) -> i64
```
- `nand_bus_sw` — wraps a `NandDevice`; `reg_write(CMD,80h)` etc. drive the device state machine;
  DMA registers move the staged buffer to/from the device. **Used on host AND bare-metal.**
- `nand_bus_mmio` — `reg_write`=`store32(base+off,val)`, `reg_read`=`load32(base+off)` to a real
  controller MMIO base. **Future** (see §10).

**Controller features** (in `nand_ctrl`, above the bus): **DMA** page transfer (data register ↔
host buffer, with `DMA_CTRL` start + `IRQ_STATUS` done — offloadable per research §12);
**ECC** compute on program / check on read (controller owns the codeword; driver reads
`ECC_STATUS`); optional **RAIN/XOR** parity stripe hook.

---

## 4. FIL driver rewrite — `fil.spl` becomes an ONFI driver

The FIL public API to the FTL stays identical (`program`/`read`→`FilRead`/`erase`/`block_bad`/…),
so **FTL and HIL are unchanged**. Internals become register sequences over `NandBus`:

```
program(ppn,lba,seq,data):
    if bbt.is_bad(block(ppn)): return NAND_BAD_BLOCK
    ctrl.dma_to_device(buffer{data,oob_lba,oob_seq})        # DMA + ECC compute
    bus.reg_write(CMD, 0x80); push 5 ADDR cycles(ppn)
    bus.reg_write(CMD, 0x10); poll RB until ready (busy = tPROG ticks)
    st = bus.reg_read(STATUS); if st & FAIL: retire block; return NAND_PROG_FAIL
    NAND_OK

read(ppn) -> FilRead:
    bus.reg_write(CMD, 0x00); push 5 ADDR cycles(ppn); bus.reg_write(CMD, 0x30)
    poll RB until ready (busy = tR ticks)
    ctrl.dma_from_device(buffer)                            # DMA out + ECC check
    code = bus.reg_read(ECC_STATUS)                         # OK/FIXED/FAIL
    FilRead{data, lba, seq, code}

erase(blk): CMD 60h → 3 row ADDR → CMD D0h → poll RB → STATUS FAIL → retire on fail
```

`bbt` (bad-block table) stays in the controller/driver layer; the device exposes only
factory-bad markers via STATUS/READ-ID.

---

## 5. Asynchronous media + the reactor (the coroutine payoff)

With busy-timing, media ops no longer complete instantly. The cooperative reactor
(`firmware.service` / `hil.tick`) gains a real polling loop:

```
issue op → device BUSY (tR/tPROG/tBERS down-counter) → tick the device clock each reactor pass
        → R/B# ready → IRQ_STATUS done → resume the waiting WriteTask/ReadTask (its PH_* phase)
```
This is where the `fw_pool` state-machine task contexts earn their keep: a task parks at
`PH_PROGRAM` until R/B# is ready, with a **per-command deadline** (research §10.3) so a stuck
device → timeout → channel reset → retry/bad-block escalation can be tested. Add a
`nand_clock` tick to `firmware.service` and a `deadline_tick` on each task.

---

## 6. Power-fail testing through the seam

The device model injects a crash at any ONFI step (`inject_powerfail(at_step)`): partial page
program, interrupted erase, status-before-ready. The existing crash/recover self-tests and
`sim_main`'s power-fail phase then run *through the controller seam*, proving the
committed-prefix property holds when the media itself fails mid-operation — a stronger test than
today's "drop the RAM L2P".

---

## 7. No-alloc constraint (bare-metal rv32)

Bare-metal `-bios none` has no heap, so the device model + buffers must have a **fixed-storage**
variant (no `[i64].push()`): static/global arrays sized at the (small) bare-metal geometry, or
a compile-time geometry constant. Keep the **`NandBus` interface identical** between builds; only
the backing storage differs (alloc on host, fixed on metal).

> **Correction (2026-06-29).** An earlier draft claimed an in-progress
> `examples/09_embedded/simpleos_nvme_fw/baremetal_rv32/` directory was the seed of this variant
> and proved the seam survives the no-heap target. **That directory does not exist** (only `fw/`
> and `emu/` subdirs do) and the Simple firmware was **not** booted on rv32. What exists today is
> a *separate, self-contained C* NAND/FTL demo that boots on `qemu-system-riscv32 -bios none`
> (`ALL RV32 NAND CHECKS PASS`) with UART output via `rt_mmio_write8(0x10000000, …)` — a toolchain
> + boot-path proof only, not the Simple firmware. The no-alloc rv32 port remains future work.

---

## 8. Module plan

| Module | Status | Responsibility |
|--------|--------|----------------|
| `nand_device.spl` | **new** | emulated chip: media + ONFI state machine + busy timing + fault/endurance/power-fail injection |
| `nand_bus.spl` | **new** | `NandBus` trait + register offset constants + ONFI command/status constants |
| `nand_bus_sw.spl` | **new** | software bus: drives a `NandDevice` from register writes (host + bare-metal) |
| `nand_ctrl.spl` | **new** | controller layer over the bus: DMA page transfer, ECC compute/check, IRQ/done |
| `fil.spl` | **rewrite** | FIL becomes an ONFI driver over `nand_ctrl`; same public API to FTL |
| `fil_nand.spl` | **retire/fold** | logic absorbed into `nand_device`; keep as the v1 reference or delete |
| `fil_ecc.spl` | reuse | ECC codeword math, now owned by `nand_ctrl` |
| `fil_badblock.spl` | reuse | bad-block table, stays in the driver |
| `nand_bus_mmio.spl` | **future** | real MMIO load/store backend (HW / QEMU controller) |
| `ftl_*`, `hil_*`, `firmware`, `fw_pool` | unchanged | FTL/HIL/reactor untouched (API-stable) |

---

## 9. Phased rollout (parallel agents, Opus review per phase; gate = `bin/simple run`)

- **E1 — Device model.** `nand_device` + ONFI state machine + STATUS/R/B + fault injection.
  Sonnet builder; tests: each ONFI sequence (program/read/erase/status/reset/id), fault paths.
- **E2 — Bus + controller.** `nand_bus`/`nand_bus_sw` + `nand_ctrl` (DMA, ECC, IRQ). Sonnet ×1–2;
  tests: register-level program/read/erase round-trip, DMA transfer, ECC OK/FIXED/FAIL.
- **E3 — FIL driver swap.** Rewrite `fil` over `nand_ctrl`; **re-run `test_fw` + `sim_main` green
  unchanged** (FTL/HIL must not notice). This is the conformance gate.
- **E4 — Async timing + reactor.** Busy-time counters, R/B polling in `firmware.service`,
  per-command deadlines + timeout→reset recovery. Add timing/timeout specs.
- **E5 — Bare-metal rv32.** No-alloc device variant booting on `qemu-system-riscv32 -machine virt
  -cpu rv32`, exercising program/read/erase + write→crash→recover, UART PASS transcript.
- **E6 — (stretch) real bus.** `nand_bus_mmio` + a memory-mapped NAND-controller device model
  added to a QEMU machine (virt has none), to drive the *same* driver over real MMIO.

Each phase: disjoint files, Opus review (correctness + no-fake-green + API-stability of `fil`),
commit + push from the worktree.

---

## 10. Acceptance

The emulated-NAND work is done when: `fil` drives the `NandDevice` purely through ONFI register
sequences over `NandBus`; `test_fw` + `sim_main` stay green with FTL/HIL unchanged; media ops are
asynchronous (busy-timed) and the reactor polls R/B# with per-command deadlines; fault/power-fail
injection drives the recovery tests through the seam; and a no-alloc rv32 build boots on
`qemu-system-riscv32` exercising the device with a UART PASS transcript. `nand_bus_mmio` + a QEMU
controller device remain an explicitly-marked stretch (QEMU `virt` has no NAND controller).
