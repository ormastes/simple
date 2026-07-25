# NVMe SSD Firmware + Host/Device Emulator — Operator Guide

Two pure-Simple deliverables under `examples/09_embedded/simpleos_nvme_fw/`, both
**host-runnable simulations** gated by `bin/simple run` (the `check` typecheck path is
deliberately avoided — see the caveats below):

1. **`fw/`** — a layered NVMe SSD **firmware** simulation: HIL / FTL / FIL plus an NVMe
   controller front end (admin + multi IO queue) driving an ONFI NAND device model.
2. **`emu/`** — a pure-Simple NVMe **host-interface ↔ device-interface emulator** with a
   settable memcpy/DMA seam on both sides, an ONFI NAND, domain newtypes, and Lean4 proofs.

> **Mostly simulation.** The main firmware and emulator are host-runnable simulations. The
> rv32 direct-smoke path is fail-closed and boots under QEMU only after
> `build/nvme_fw_rv32.elf` is produced; the full no-alloc firmware port is still not complete
> (see "rv32 status").

---

## 1. The firmware (`fw/`)

A bare-metal-shaped NVMe SSD controller firmware written as a host-runnable simulation of the
full data path: host NVMe queues → translation layer → flash media. Geometry: 4 planes ×
16 blocks × 64 pages = 4096 physical pages, 3072 surfaced LBAs, one byte/page payload.

### Layered architecture (MDSOC+)

<!-- sdn-diagram:id=nvme_fw_layers -->
```
                  host NVMe SQ/CQ rings  (admin qid-0 + IO qid-1..N)
                              │
  ┌───────────────────────────▼───────────────────────────────────────────────┐
  │ NVMe CONTROLLER FRONT END                                                   │
  │   nvme_admin   Identify (Ctrl/NS), Get/Set Features, Get Log Page (SMART),  │
  │                Create/Delete IO SQ & CQ   (CQ-before-SQ, bound-CQ rules)    │
  │   nvme_qset    up to MAX_IO_QUEUES SQ/CQ pairs, fair round-robin scheduler  │
  │   nvme_controller  admin_process + io_process → FTL                         │
  └───────────────────────────┬───────────────────────────────────────────────┘
                              │  (legacy single-queue path: hil + firmware reactor)
  HIL ┌────────────────────────▼──────────┐  hil_queue · hil_command · fw_pool · hil
      │ fetch → validate → dispatch →     │  (decode; generation-handle task context;
      │ complete                          │   SQ→CQ cooperative reactor)
      └────────────────────────┬──────────┘
  FTL ┌────────────────────────▼──────────┐  ftl_map (DFTL write-back cache) · ftl_band
      │ L2P map · log alloc · WAL · GC ·  │  (log allocator + valid bitmap) · ftl_journal
      │ RAIN recover · crash recovery     │  (WAL + checkpoint + A/B superblock) · ftl_gc
      └────────────────────────┬──────────┘  (greedy victim) · ftl (write/read/trim/recover/gc) · rain (per-stripe XOR parity: rain_seal / rain_recover_channel)
  FIL ┌────────────────────────▼──────────┐  fil_nand_device (ONFI NAND *device*) · fil_ecc
      │ program/read/erase + ECC +        │  · fil_badblock · fil (ECC-verified reads,
      │ bad-block remap                   │   bad-block retirement)
      └───────────────────────────────────┘
  firmware.spl — cooperative reactor: service cycle = drain queues + background GC below the
  free-block watermark; checkpoint; power_cycle.
```

The FIL runs on the **ONFI device** (`fil_nand_device.spl`), a protocol-accurate NAND chip
model (CMD/ADDR/DATA latch + `exec()` state machine: READ 00h/30h, PROGRAM 80h/10h main+spare,
ERASE 60h/D0h, STATUS 70h, RESET FFh; status register, OOB {lba,seq}, no-overwrite rule,
bit-flip + bad-block + one-shot fault injection). It is a faithful drop-in for the behavioural
`fil_nand.Nand` (same `program/read_page/erase_block/...` seam), so every write/read/GC-erase/
recovery-OOB-scan goes through the real ONFI handshake.

**Live thermal (P7).** The controller front end now carries a `pt: PowerThermal` model that is
ticked on every program/read. Get Log Page (SMART) reports the **live** composite temperature and
ORs in the thermal critical-warning bit from that model — replacing the former hardcoded
`temperature: 313`.

### Run / verify

```bash
B=bin/simple
$B run examples/09_embedded/simpleos_nvme_fw/fw/test_fw.spl    # -> ALL FIRMWARE SELF-TESTS PASS  (1174 assertions)
$B run examples/09_embedded/simpleos_nvme_fw/fw/sim_main.spl   # -> ALL END-TO-END CHECKS PASS
$B run examples/09_embedded/simpleos_nvme_fw/fw/nvme_main.spl  # -> ALL NVME CONTROLLER E2E CHECKS PASS
$B run examples/09_embedded/simpleos_nvme_fw/fw/rain_check.spl      # -> RAIN OK
$B run examples/09_embedded/simpleos_nvme_fw/fw/rain_ftl_check.spl  # -> RAIN-FTL OK   (whole-channel failure survived)
$B run examples/09_embedded/simpleos_nvme_fw/fw/thermal_check.spl   # -> THERMAL OK
```

- **`test_fw.spl`** — full self-test suite, 1174 `PASS:` assertions across all modules (now
  including RAIN, thermal, sandbox, hooks selftests).
- **`sim_main.spl`** — single-queue end-to-end: 128 writes → read-back → overwrite-all (write
  amplification) → garbage collection (reclaim stale blocks, logical view preserved) → trim →
  power-fail + recovery (committed state survives, trim stays trimmed).
- **`nvme_main.spl`** — admin-driven controller acceptance: host bring-up (Identify → Features →
  Create CQ→SQ) → multi-queue IO with round-robin → negative cases (SQ→missing-CQ rejected,
  invalid namespace rejected, delete-bound-CQ rejected) → reverse-order teardown → SMART log
  (live thermal temperature + critical-warning) → power-cycle survival.
- **`rain_check.spl` / `rain_ftl_check.spl` / `thermal_check.spl`** — the P7/P8 wiring demos:
  `RAIN OK` (standalone per-stripe XOR parity), `RAIN-FTL OK` (256 LBAs survive a whole-channel
  uncorrectable failure, rebuilt in place), `THERMAL OK` (live composite temperature + critical
  warning). All three are also gated in the system spec.

Modules are flat in `fw/`, imported with the **bare** form (`use nvme_types.*`). No module
contains `fn main()` (two imported mains collide); each exposes `fn <module>_selftest() -> i64`
returning a failure count. See `fw/CONVENTIONS.md` for the two compiler-bug workarounds in force
(the `check` typecheck-blowup, and a conditional first-param ×8 interpreter bug isolated to
`ftl_journal.append`).

Additional firmware modules: `power_thermal.spl` (power-state + thermal model, wired as P7),
`rain.spl` (RAIN per-stripe XOR parity — `rain_seal` / `rain_recover_channel`, wired as P8), plus
`sandbox.spl` / `hooks.spl` (sandboxed policy hooks).

> **Wired vs. shelf (honest status).** This is a hardware-**faithful simulation**, not a
> silicon-shippable binary — "production level" in the literal sense is not done. Of the gap-closure
> items: **P1** (`fil_fmc`), **P2** (`fil_scheduler`), **P3** (SECDED ECC floor), **P4**
> (segmented-PRP floor), **P5** (DRAM/map-cache floor), **P6** (cooperative ownership floor),
> **P7** (`power_thermal`), and **P8** (`rain`) are wired floors in the live path. **P9** has a
> fail-closed rv32 direct-smoke recipe; the QEMU PASS marker requires a produced
> `build/nvme_fw_rv32.elf`, and the full 22-module no-alloc firmware port remains open.
> Canonical table:
> `doc/03_plan/hardware/nvme_fw_gap_closure_plan.md` § "Integration status".

---

## 2. The emulator (`emu/`)

A pure-Simple NVMe SSD emulator split into a **host interface** and a **device interface** that
exchange data *only* across a **settable memcpy/DMA seam**, backed by a RAM-backed ONFI NAND and
a compact FTL. No C anywhere.

<!-- sdn-diagram:id=nvme_emu_seam -->
```
  HOST INTERFACE           SEAM (RAM-backed shared mem)          DEVICE INTERFACE
  host_write / host_read  --host memcpy-->  SharedMem  <--dev memcpy--  dev_step
  host_fetch_data                          (data buffers)               FTL → ONFI NandArray
       \_____________ NvmeEmu owns shared + ftl + nand + both DMA ports _____________/
```

**Geometry:** 2 channels × 2 banks × 2 planes × 2 blocks × 8 pages = **128 physical pages**,
96 surfaced LBAs, 4 i64 words/page. `ppn = ((((ch*2+bank)*2+plane)*2+block)*8+page)`.

| file | role |
|------|------|
| `nvme_ct.spl` | locked interface: domain **newtypes** (Lba/Ppn/Ch/Bank/Plane/Block/Page/Cid/Qid/Addr), geometry, address codec, Command/Completion |
| `nand_onfi.spl` | `NandArray` — ONFI command/address/data handshake per channel, RAM media, OOB, fault injection |
| `nvme_shared.spl` | `SharedMem` — the RAM-backed DMA region (bounds-checked store/load) |
| `nvme_memcpy.spl` | `Dma` — the **settable** memcpy seam (`set_copy`; default + fault-injecting copies) |
| `ftl_emu.spl` | compact L2P FTL over the NAND (log append; no GC — minimal by design) |
| `nvme_host.spl` / `nvme_device.spl` | `HostPort`/`DevPort` + the `NvmeEmu` owner struct |
| `nvme_emu_main.spl` | end-to-end demo + the memcpy-seam fault-injection proof |
| `proofs/*.lean` | Lean4: Addr, Memcpy, Queue, Resource |

### Run / verify

```bash
B=bin/simple
$B run examples/09_embedded/simpleos_nvme_fw/emu/nvme_emu_main.spl   # -> EMU E2E PASS  (38 checks)
```

> **Expected noise.** This run prints `[WARN] ... Unknown type: Ppn` and
> `[INFO] JIT compilation failed, falling back to interpreter`. These are **not** failures —
> they are caveat (a) below (newtypes do not lower under JIT, so the run uses the interpreter,
> where results are correct). The final line is `EMU E2E PASS`.

**Per-module selftests (116 assertions total).** There is no single committed harness that runs
all four — each is a module-level `*_selftest() -> i64` (failure count). To exercise them
locally, create a temporary file *inside `emu/`* (so the bare `use` imports resolve) and run it:

```simple
# emu/_selftests.spl  (temporary; uses print, not the deprecated println)
use nand_onfi.*
use nvme_memcpy.*
use ftl_emu.*
use nvme_device.*
fn main():
    val a = nand_array_selftest()    # NAND_ONFI_SELFTEST PASS    (36 asserts)
    val b = shared_memcpy_selftest() # PASS shared_memcpy_selftest (25 asserts)
    val c = ftl_selftest()           # FTL_EMU_SELFTEST PASS       (22 asserts)
    val d = nvme_device_selftest()   # NVME_DEVICE_SELFTEST PASS   (33 asserts)
    print "total failures = {a+b+c+d}"   # 0
```

```bash
$B run examples/09_embedded/simpleos_nvme_fw/emu/_selftests.spl   # each module prints its PASS line; 116 PASS asserts, 0 fail
```

### The memcpy/DMA seam — and why the fault-injection demo matters

Data crosses the host↔device boundary only through a `Dma` whose `copy` is a swappable
fn-field. `NvmeEmu` re-plugs each side independently:

```simple
emu.set_host_memcpy(\s, o, n: dma_copy_corrupt(s, o, n))   # corrupt host side
emu.set_dev_memcpy(\s, o, n: dma_copy_corrupt(s, o, n))    # corrupt device side
# ... restore with \s,o,n: dma_copy_words(s,o,n)
```

`nvme_emu_main` steps 4 and 5 **prove the seam is load-bearing, not decorative**: it plugs a
corrupting copy (`dma_copy_corrupt` flips the FIRST transferred word, `w → w+1`) on the device
side, writes LBA 6, restores a clean copy, reads back, and asserts word0 is corrupted
(`1 → 2`) while words 1–3 are intact — then repeats on the host side (`900 → 901`). If the
memcpy were *not* genuinely on the data path, the corruption could not appear in NAND/read-out.
(Implementation note from the bug below: the fn-field must be assigned a **lambda** wrapping a
named fn, and invoked by binding to a local first — `var f = me.copy; f(...)`.)

---

## 3. Custom typing — and the honest caveat

The emulator uses domain **newtypes** (`Lba`, `Ppn`, `Ch`, `Bank`, …) pervasively in
signatures and records to document intent.

> **Caveat (a): newtypes are NOT compiler-enforced on this binary.** A `Ppn` is accepted where
> an `Lba` is expected, and mixed-newtype arithmetic erases the wrapper — under **both** `check`
> and `run`. They are documentation only; there is no nominal distinctness, and the JIT cannot
> lower them (hence the interpreter fallback and the `Unknown type` warnings above). Filed:
> `doc/08_tracking/bug/newtype_run_path_and_enforcement_gaps_2026-06-29.md`. The *enforced*
> guarantees live in the Lean4 proofs, not the type system.

---

## 4. Lean4 verification — what is proven, and what it does NOT claim

The four `emu/proofs/*.lean` files prove properties **of the algorithms**, run standalone:

```bash
export PATH="$HOME/.elan/bin:$PATH"
for f in Addr Memcpy Queue Resource; do
  lean examples/09_embedded/simpleos_nvme_fw/emu/proofs/$f.lean   # each exits 0, no `sorry`
done
```

| proof | property | corresponds to (Simple) |
|-------|----------|--------------------------|
| `Addr.lean` | PPA↔ppn is a bijection onto [0,128) | `nvme_ct.ppa_to_ppn` + `ppn_channel/bank/plane/block/page` (same formula) |
| `Memcpy.lean` | a transfer never touches an index outside the region | `nvme_shared.SharedMem.store/load` — bounds-checks every index against `[0,SHARED_WORDS)` |
| `Queue.lean` | the monotonic head cursor never reads out of bounds | `nvme_device` SQ/CQ append columns + guarded `*_head` reap |
| `Resource.lean` | (a) FTL allocator hands out valid, never-reused pages; (b) distinct PRP buffers don't overlap | (a) `ftl_emu.Ftl.write` cursor allocator; (b) `nvme_shared` regions / distinct PRPs in `nvme_emu_main` |

> **Caveat (b): the proofs are standalone, hand-transcribed algorithm models.** The math is
> hand-transcribed from the Simple logic; there is **no mechanical link** between the proofs and
> the executed bytes (the compiler's `@verify` / gen-lean MIR→Lean path does not yet handle this
> code — same bug doc as above). A proof certifies "this *algorithm* is correct, verified
> independently by Lean", **not** "the compiled interpreter cannot deviate". Each proof is
> written to mirror a specific Simple code path, and where a proof has a precondition the code is
> written to establish it at runtime (e.g. `SharedMem` now bounds-checks to satisfy `Memcpy`).
> The firmware (`fw/`) now ships its own standalone Lean4 proofs as well
> (`fw/proofs/{Alloc,Recover,Gc,Hooks,Fmc,Rain}.lean`) — like the emulator proofs above, these are
> hand-transcribed algorithm models, not mechanically linked to the executed bytes.

---

## 5. rv32 bare-metal status (read this plainly)

Default `fw_rv32/build.shs` is the small direct rv32 ELF recipe; it avoids rebuilding the Rust
seed and does not compile the full Simple firmware graph. Build the ELF before treating this as
boot evidence:

```sh
NVME_RV32_BUILD_TIMEOUT_SECS=60 sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs
sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/boot.shs build/nvme_fw_rv32.elf
```

When the ELF exists, the boot must print `ALL RV32 NVME FW CHECKS PASS` and exit `RESULT: PASS`;
`boot.shs --self-test` separately proves the wrapper fails closed on bad serial output. This is
P9 direct-smoke evidence, not the full firmware port. Set
`NVME_RV32_BUILD_OS_BOOT=1` only when intentionally exercising the slower full rv32 OS boot/source
graph; the full 22-module no-alloc port remains open.

---

## 6. Provenance / further reading

- Firmware build status & module map: `examples/09_embedded/simpleos_nvme_fw/fw/BUILD_STATUS.md`,
  `fw/README.md`, `fw/CONVENTIONS.md`.
- Production / wired-vs-shelf status: `examples/09_embedded/simpleos_nvme_fw/fw/PRODUCTION_STATUS.md`
  and the wired-vs-shelf "Integration status" table in
  `doc/03_plan/hardware/nvme_fw_gap_closure_plan.md`.
- Emulator: `examples/09_embedded/simpleos_nvme_fw/emu/README.md`, `.spipe/nvme_emu/state.md`.
- Research: `doc/01_research/hardware/nvme_firmware/`.
- Build plans (and what is done vs. future): `doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md`,
  `doc/03_plan/hardware/nvme_fw_emulated_nand_plan.md`.
- rv32 native-build blocker: `doc/08_tracking/bug/native_build_rv32_baremetal_silent_255_2026-06-30.md`.
- Newtype + Lean caveats: `doc/08_tracking/bug/newtype_run_path_and_enforcement_gaps_2026-06-29.md`.
