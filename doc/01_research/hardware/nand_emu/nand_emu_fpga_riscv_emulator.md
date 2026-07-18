# NAND Chip Emulator (K9F8G08X0M-compatible) — FPGA + RAM + Dedicated RISC-V Core

**Target:** an optional peripheral/subsystem of the Simple RV32/RV64 core family
(`simple-lang/simple`), written in Simple: RTL through the VHDL-2008 backend
subset, firmware through the baremetal path (`nogc_async_mut_noalloc`).

**Working name:** `nand_emu` · **Module id:** `hw.nand_emu` · **Config key:** `soc.nand_emu`

---

## 0. Goal in one paragraph

Present a **pin-accurate Samsung K9F8G08X0M NAND interface** to an external host
controller (real SoC, or another Simple RV core), while the array behind those
pins is not a bit array but a **per-cell threshold-voltage (Vt) byte array in
RAM**. Because every cell carries an 8-bit analog-ish level instead of one bit,
the emulator can reproduce the phenomena that real NAND firmware must survive —
program disturb, read disturb, retention charge loss, over-erase, wear-induced
distribution widening, sudden power-off mid-program — and therefore lets you
develop and regression-test **recovery and prevention logic** (read retry,
soft-decision LLR, refresh, wear leveling, block retirement) against a
deterministic, replayable device. The address space is deliberately **shrunk**
(the 5-cycle address protocol is kept intact on the pins; only low-order bits are
decoded) so the Vt array fits in FPGA BRAM or a modest DDR3.

---

## 1. Device facts extracted from the datasheet (rev 1.0)

These are the contract the emulator must honor. Source: `ds_k9f8g08x0m_rev10.pdf`.

### 1.1 Geometry

| Item | Value |
|---|---|
| Density | 8,448 Mbit (8 Gb + 256 Mb spare) |
| Page | 4,096 + 128 = **4,224 B** |
| Block | 64 pages = 256 KB + 8 KB |
| Blocks | 4,096 (2 planes × 2,048, even/odd by A18) |
| Pages | 262,144 |
| Sector (EDC unit) | 528 B = 512 main + 16 spare, **8 sectors/page** |
| Column addr | A0–A12 (0…4,223) |
| Row addr | A13–A30 (18 bits) |
| Valid blocks | ≥ 4,016 of 4,096 (up to 80 factory-bad) |
| Nop | ≤ 4 partial programs per page, **LSB→MSB page order enforced** |
| Endurance | 100 K P/E with 1 bit / 512 B ECC |

### 1.2 Address cycle map (must be reproduced exactly)

```
cyc1: A0  A1  A2  A3  A4  A5  A6  A7
cyc2: A8  A9  A10 A11 A12 L   L   L
cyc3: A13 A14 A15 A16 A17 A18 A19 A20
cyc4: A21 A22 A23 A24 A25 A26 A27 A28
cyc5: A29 A30 L   L   L   L   L   L
```
Erase uses cyc3–5 only. A19 selects plane in two-plane addressing;
A13–A18 are ignored by erase.

### 1.3 Command set

| Function | 1st | 2nd | OK during busy |
|---|---|---|---|
| Read | 00h | 30h | |
| Read for Copy-Back | 00h | 35h | |
| Read ID | 90h | – | |
| Reset | FFh | – | ✔ |
| Page Program | 80h | 10h | |
| Copy-Back Program | 85h | 10h | |
| Block Erase | 60h | D0h | |
| Random Data Input | 85h | – | |
| Random Data Output | 05h | E0h | |
| Read Status | 70h | – | ✔ |
| Read EDC Status | 7Bh | – | ✔ |
| Read Status 2 | F1h | – | ✔ |
| Two-Plane Read | 60h..60h | 30h | |
| Two-Plane Read for Copy-Back | 60h..60h | 35h | |
| Two-Plane Random Data Out | 00h..05h | E0h | |
| Two-Plane Page Program | 80h..11h | 81h..10h | |
| Two-Plane Copy-Back Program | 85h..11h | 81h..10h | |
| Two-Plane Block Erase | 60h..60h | D0h | |
| 2 KB Page Program | 80h..11h | 80h..10h | |
| 2 KB Copy-Back Program | 85h..11h | 85h..10h | |

Between 11h and 80h/81h/85h only 70h / F1h / FFh are legal. Any other command is
undefined — the emulator **logs a protocol violation** rather than guessing.

### 1.4 Status registers

* **70h**: I/O0 pass/fail (0=pass), I/O6 ready/busy (0=busy), I/O7 WP (0=protected).
* **F1h**: I/O0 chip P/F, I/O1 plane0 P/F, I/O2 plane1 P/F, I/O6, I/O7 as above.
* **7Bh** (copy-back only): I/O0 P/F, I/O1 EDC error, I/O2 EDC validity, I/O6, I/O7.
* After reset with WP high the status register reads **C0h**.

### 1.5 ID

`90h` + addr `00h` → **EC D3 10 A6 64** (maker, device, 3rd, 4th, 5th).
4th byte `A6h` encodes 4 KB page / 256 KB block / 16 B per 512 B redundancy /
x8 / 25 ns serial access. The emulator exposes these as registers so a shrunk
profile can still *report* the real ID (host firmware under test usually keys off
the ID) while physically being small.

### 1.6 Timing budget (3.3 V part) — the hard part on FPGA

| Param | Symbol | Limit |
|---|---|---|
| Write cycle | tWC | ≥ 25 ns |
| WE pulse / high | tWP / tWH | ≥ 12 / ≥ 10 ns |
| CLE/ALE/data setup | tCLS/tALS/tDS | ≥ 12 ns |
| … hold | tCLH/tALH/tDH | ≥ 5 ns |
| Addr→data load | tADL | ≥ 100 ns |
| Read cycle | tRC | ≥ 25 ns |
| **RE access** | **tREA** | **≤ 20 ns** |
| CE access | tCEA | ≤ 25 ns |
| RE high→Hi-Z | tRHZ | ≤ 100 ns |
| WE high→busy | tWB | ≤ 100 ns |
| WE high→RE low | tWHR | ≥ 60 ns |
| RE high→WE low | tRHW | ≥ 100 ns |
| Cell→register | tR | ≤ 25 µs |
| Program | tPROG | 200 µs typ / 700 µs max |
| Dummy busy (2-plane) | tDBSY | 0.5 µs typ / 1 µs max |
| Erase | tBERS | 1.5 ms typ / 2 ms max |
| Reset | tRST | 5 / 10 / 500 µs (read/prog/erase) |

`tREA ≤ 20 ns` is the single constraint that dictates the RTL structure:
**the byte must already be sitting in the IOB output register before RE falls.**
Everything else has slack measured in microseconds and can go to software.

---

## 2. System architecture

```
              ┌──────────────────────── FPGA ─────────────────────────────┐
 host         │                                                           │
 controller   │  ┌────────────┐   ┌──────────────┐    ┌────────────────┐  │
 (DUT)        │  │ PIN LAYER  │   │  PAGE BUFFER │    │  ACCEL BLOCK   │  │
 ──IO[7:0]────┼─▶│  sync/edge │──▶│  2 × 4224 B  │◀──▶│  sense engine  │  │
 ──CLE/ALE────┼─▶│  latch fsm │   │  dual-port   │    │  program engine│  │
 ──/CE /RE────┼─▶│  out-reg   │◀──┤   BRAM       │    │  noise LFSR    │  │
 ──/WE /WP────┼─▶│  timing chk│   └──────────────┘    │  EDC/ECC unit  │  │
 ──R/B────────┼──┤  R/B drv   │            ▲          └───────┬────────┘  │
              │  └─────┬──────┘            │                  │           │
              │        │ event ring        │  AXI/TL          │           │
              │        ▼                   ▼                  ▼           │
              │   ┌───────────────────────────────────────────────────┐   │
              │   │  DEDICATED RISC-V CORE  (Simple RV32I/RV64I)      │   │
              │   │  firmware: cmd FSM, geometry, physics, faults,     │   │
              │   │            status regs, EDC policy, trace          │   │
              │   └───────────────────────────────────────────────────┘   │
              │        │                                                  │
              └────────┼──────────────────────────────────────────────────┘
                       ▼
             ┌───────────────────────────────┐
             │  CELL RAM (BRAM or DDR3)      │
             │  Vt[cell] : u8  ← 1 B / cell  │
             │  page meta / block meta       │
             └───────────────────────────────┘
```

**Division of labor (this is the key architectural decision):**

| Layer | Owns | Why |
|---|---|---|
| RTL pin layer | Anything with a sub-100 ns deadline: WE/RE edges, latch classification, column counter, output register, Hi-Z, R/B drive, timing violation capture | Cannot be done in software at 25 ns cycle time |
| RTL accel block | Bulk streaming over the Vt array: sense (Vt→bit pack), program (ISPP add + noise), fill, disturb-delta apply | 33,792 cells/page; a scalar core cannot touch them inside tR |
| RISC-V firmware | *Everything else*: command legality, address decode, geometry shrinking, when/what to sense, ISPP parameters, disturb/retention/wear policy, bad-block map, EDC status, fault injection, tracing | "Let SW handle detail" — all of it is µs-scale and needs to be editable without resynthesis |

The accel block is intentionally **policy-free**: it is a set of vector
primitives. The firmware issues them. Any behavior change is a firmware rebuild
(seconds), not a bitstream rebuild (minutes to hours).

---

## 3. The Vt cell model

### 3.1 Encoding

One unsigned byte per cell:

```
Vt(code) = (code - 128) × 25 mV      → range −3.200 V … +3.175 V, step 25 mV
```

| Meaning | Code | Vt |
|---|---|---|
| Deep erased (over-erase tail) | 40 | −2.20 V |
| Erased distribution mean | 88 | −1.00 V |
| Erase verify level (EV) | 116 | −0.30 V |
| **Default read reference (Vread)** | **128** | **0.00 V** |
| Program verify level (PV) | 148 | +0.50 V |
| Programmed distribution mean | 168 | +1.00 V |
| Over-programmed | 220 | +2.30 V |
| Saturated / broken cell | 255 | +3.175 V |

**Read rule (SLC):** the cell conducts when `Vt < Vread`, so

```
bit = 1 (erased)   if code <  vref
bit = 0 (program)  if code >= vref
```

This matches the datasheet's erased state of FFh and the "internal write verify
detects only errors for 1s not successfully programmed to 0s" note.

### 3.2 Why a byte per cell buys you the recovery/prevention work

| Firmware feature under test | What the Vt byte makes possible |
|---|---|
| **Read retry** | Re-sense the same page with `vref + offset[k]` from a retry table and get *genuinely different data*, because the distributions actually shifted |
| **Soft-decision / LLR** | 3–7 senses at neighboring vrefs → per-bit confidence; feed an LDPC/BCH soft decoder |
| **Retention management** | Charge loss drifts programmed cells down; after enough emulated time the 0s start reading as 1s — exactly the failure real firmware refreshes against |
| **Read disturb** | Vpass on unselected pages nudges erased cells up; a read-disturb counter → refresh policy has something real to trigger on |
| **Program disturb** | Neighbor pages in the same block gain ΔVt during program |
| **Wear / endurance** | P/E cycle count widens σ and raises the erase floor; blocks genuinely start failing near 100 K |
| **Sudden power-off** | Abort ISPP mid-loop → cells parked between distributions; on next read they are neither reliably 0 nor 1 (the classic SPO signature) |
| **Over-erase detection** | Erase without the soft-program step drives cells below the tail; leakage/GIDL behavior emulatable |
| **Copy-back accumulation** | EDC 1 bit/528 B is real; copying a page whose Vt already drifted accumulates errors, which is precisely why the datasheet added EDC |

### 3.3 Per-cell noise without per-cell storage

Storing σ per cell would need a second byte. Instead, per-cell variation is
**derived deterministically**:

```
seed(cell) = splitmix32(row ⊕ (col << 3) ⊕ bit_index ⊕ CHIP_SEED)
```

The same cell always gets the same intrinsic offset, trim, and wear
susceptibility, so runs are reproducible and diffable, and the array stays at
exactly 1 B/cell. `CHIP_SEED` is a register: change it and you get a different
"physical die" with the same firmware.

### 3.4 Lazy drift (critical optimization)

Retention and disturb are **additive** in this model, so they commute and can be
applied at read time instead of eagerly sweeping megabytes:

```
effective_vt = stored_vt
             + retention_delta(Δt_since_program, pe_cycles, stored_vt)
             + disturb_delta(read_disturb_count, program_disturb_count)
```

Per-page metadata carries `last_program_time`, `read_disturb_count`,
`program_disturb_count`; per-block carries `pe_cycles`, `last_erase_time`,
`bad_flag`. A neighbor-page program therefore costs one counter increment, not a
4 KB read-modify-write. A "bake for 1 year at 85 °C" command is a single clock
advance, not a full-array pass. The deltas are *materialized* into the stored Vt
only when a page is programmed or erased (or on an explicit `MATERIALIZE`
debug command, useful for checkpointing).

---

## 4. Address shortening

The pin protocol is untouched: the host still drives 2 column + 3 row cycles and
still sees ID `EC D3 10 A6 64`. Only decoding is shrunk.

```
col_eff = col & COL_MASK                       (COL_MASK = page_bytes − 1, page-shaped)
row_eff = (row & ROW_MASK) | ROW_BASE          (or aliased / trapped)
```

`OOB_POLICY` register selects what happens when `row & ~ROW_MASK != ROW_BASE`:

| Policy | Behavior |
|---|---|
| `ALIAS` | wrap into the window (default; smallest surprise for FTL bring-up) |
| `WINDOW` | only the window is backed; outside → reads FFh, status pass, no cell state |
| `TRAP` | raise an event; firmware decides — return a synthetic factory-bad block, or fail status, or log and alias |

`TRAP` is the interesting one: it lets you make "the 4,096-block chip" behave as
if 4,080 blocks are outside the model while still exercising the host's bad-block
scan over the *full* address range.

### 4.1 Shrink profiles

| Profile | Page | Pages/blk | Blocks | Pages | **Vt RAM** | Meta | Fits |
|---|---|---|---|---|---|---|---|
| `S1 nano` | 528 B (1 sector) | 4 | 8 | 32 | **132 KB** | 1 KB | BRAM, GHDL sim |
| `S2 micro` | 528 B | 8 | 32 | 256 | **1.03 MB** | 3 KB | BRAM (mid FPGA) |
| `S3 small` | **4,224 B (8 sectors)** | 8 | 16 | 128 | **4.13 MB** | 2 KB | big BRAM / SRAM |
| `S4 medium` | 4,224 B | 16 | 64 | 1,024 | **34.6 MB** | 10 KB | DDR3 |
| `S5 large` | 4,224 B | **64 (real)** | 128 | 8,192 | **277 MB** | 76 KB | DDR3 512 MB |
| `S6 full` | 4,224 B | 64 | 4,096 | 262,144 | 8.86 GB | 2.3 MB | ✗ (documented, unbuildable) |

`Vt RAM = page_bytes × 8 × pages`.

**Recommendation:** develop on `S1`/`S2` in GHDL, run the firmware regression
suite on `S3`, run long endurance/retention campaigns on `S4`, and keep `S5` for
"does the FTL survive a realistic block count" runs. Use `S3` as the default
because it is the smallest profile that keeps the **real 8-sector / 528 B page
structure**, which copy-back EDC semantics depend on.

---

## 5. RTL design (Simple → VHDL-2008)

Written in the hardware-oriented Simple subset (see
`doc/04_architecture/vhdl_support_matrix.md`; the backend is strict fail-fast on
unsupported constructs, so keep to registers, arrays, and combinational
expressions — no dynamic allocation, no unbounded loops).

### 5.1 Pin frontend

```
# hw/nand_emu/pin_frontend.spl  (VHDL backend subset)

struct NandPins:
    io_i:    u8      # from pads
    io_o:    u8      # to pads
    io_oe:   bool    # tri-state enable
    cle:     bool
    ale:     bool
    ce_n:    bool
    re_n:    bool
    we_n:    bool
    wp_n:    bool
    rb_n:    bool    # open-drain: drive 0 or Hi-Z

enum LatchKind:
    Command
    Address
    DataIn
    Illegal

fn classify(cle: bool, ale: bool) -> LatchKind:
    match (cle, ale):
        | (true,  false) -> LatchKind.Command
        | (false, true)  -> LatchKind.Address
        | (false, false) -> LatchKind.DataIn
        | (true,  true)  -> LatchKind.Illegal
```

Requirements on this block:

1. **Two-FF synchronizers** on `cle, ale, ce_n, we_n, re_n, wp_n` (the host is
   asynchronous). `io_i` is captured combinationally at the `we_n` rising edge
   with an input delay line, not resynchronized — resynchronizing data would eat
   the tDS/tDH budget.
2. **Latch on `we_n` rising edge** while `ce_n` low. Emit `(kind, byte)`.
3. **Output pre-fetch**: on every `re_n` *rising* edge, load the next byte from
   the page buffer into the IOB output FF and increment the column counter. When
   `re_n` falls, the byte is already at the pad → `tREA` becomes the pad
   clock-to-out delay (typically 4–8 ns), comfortably inside 20 ns.
4. **`io_oe`** asserted when (`ce_n` low AND `re_n` low AND in-output-state);
   deasserted within tRHZ/tCHZ.
5. **R/B** is open-drain: drive low, never drive high.
6. **CE don't-care** support: the datasheet explicitly permits CE going inactive
   mid data-load / mid serial-access. The column counter must survive it.

### 5.2 Timing checker (do not skip this)

A small block that measures every AC parameter against the datasheet minima and
latches violations with a timestamp. It turns the emulator into a **protocol
conformance tester** for the host controller, which is often more valuable than
the storage emulation itself.

```
struct TimingViolation:
    param_id:  u8     # tWP, tWC, tADL, tWHR, tRHW, tCLS, tALS, tDS, ...
    measured:  u16    # in 100 ps ticks
    limit:     u16
    timestamp: u32
```
Violations push into the same event ring the firmware drains, tagged
`EVT_TIMING`. Optional `strict` mode: a violation forces the emulated device
into an undefined-behavior state (garbage data, random status) — because that is
what real silicon does, and firmware that only works against a forgiving model
is not validated.

### 5.3 Page buffer

2 × 4,224 B dual-port BRAM (ping-pong). Port A: pin layer, byte-wide, 1 access
per RE/WE cycle. Port B: accel block + core, 64-bit wide. Ping-pong lets the
firmware prepare the next page (copy-back, two-plane) while the host is still
clocking out the current one.

### 5.4 Accel block primitives

All are "start / busy / done+IRQ" DMA-style engines over the Vt array:

| Primitive | Operation | Rate target |
|---|---|---|
| `SENSE` | for each cell: `bit = (vt_eff < vref)`, pack 8→1 byte, into page buffer | 8 cells/cycle |
| `SENSE_SOFT` | N senses at `vref + off[k]`, produce N bitplanes | N × above |
| `PROGRAM` | for cells whose target bit is 0: ISPP loop, `vt += step + noise`, clamp, until `vt ≥ PV` or `npulse` exhausted | 8 cells/cycle/pulse |
| `ERASE` | `vt = erase_mean + noise(σ(pe_cycles))`, whole block | 8 cells/cycle |
| `ADD_DELTA` | `vt += delta` over a range (materialize disturb/retention) | 8 cells/cycle |
| `DIGEST` | CRC/histogram over a range (checkpointing, distribution plots) | 8 cells/cycle |
| `EDC` | 1 bit/528 B error detect code per sector | 1 sector/pass |

**Sense throughput check for `S3`:** 4,224 B × 8 = 33,792 cells. At 8 cells/cycle
that is 4,224 cycles = **42 µs @ 100 MHz** — over the 25 µs tR. Fixes, in order
of preference: (a) run the accel block at 200 MHz → 21 µs ✔; (b) widen to 16
cells/cycle (128-bit path) → 21 µs @ 100 MHz ✔; (c) use `MODEL` timing mode.

### 5.5 Two timing modes

| Mode | R/B behavior | Use |
|---|---|---|
| `REALTIME` | busy asserted for exactly the datasheet time (tR/tPROG/tBERS), enforced by a hardware ns timer; if the model isn't done in time → `EVT_OVERRUN` and status fail | conformance, performance measurement |
| `MODEL` | busy held until the model actually finishes; emulated-time counter still advances by the datasheet amount | complex physics, large profiles, debugging |
| `DILATE(D)` | all emulated times × D | slow hosts, logic-analyzer capture, GHDL |

`MODEL` is honest: the host firmware polls R/B or I/O6, so it tolerates longer
busy. What it *cannot* tolerate is a busy that is shorter than the model needs —
hence the overrun event.

---

## 6. Hardware/software interface

### 6.1 MMIO register map (base `NAND_EMU_BASE`, default `0x8010_0000`)

| Offset | Name | Description |
|---|---|---|
| `0x000` | `ID` | `"NEMU"` magic + version |
| `0x004` | `CTRL` | enable, soft_reset, mode(RT/MODEL/DILATE), strict_timing, wp_override |
| `0x008` | `STATUS` | fsm_state, busy, pbuf_sel, oob_pending |
| `0x00C` | `IRQ_STAT` / `0x010` `IRQ_EN` | evt_ready, sense_done, prog_done, timing_viol, overrun, oob_trap |
| `0x014` | `GEOM` | page_shift, ppb_shift, block_count, sectors_per_page |
| `0x018` | `COL_MASK` / `0x01C` `ROW_MASK` / `0x020` `ROW_BASE` / `0x022` `OOB_POLICY` | address shortening |
| `0x024` | `CHIP_ID[0..1]` | 5 ID bytes as reported to the host (defaults `EC D3 10 A6 64`) |
| `0x028` | `CHIP_SEED` | die-variation seed |
| `0x030` | `EVT_BASE` / `0x034` `EVT_SIZE` / `0x038` `EVT_HEAD` / `0x03C` `EVT_TAIL` | event ring |
| `0x040` | `RB_CTRL` | assert/deassert busy, busy_duration_ns |
| `0x044` | `TIME_LO/HI` | emulated ns counter · `0x04C` `TIME_ADVANCE` (retention jumps) |
| `0x050` | `TCHK_EN` / `0x054` `TCHK_FLAGS` / `0x058` `TCHK_CAPTURE` | timing checker |
| `0x060` | `PBUF_SEL` / `0x064` `PBUF_COL` / `0x068` `PBUF_LEN` | page buffer control |
| `0x070` | `SENSE_SRC` / `0x074` `SENSE_LEN` / `0x078` `SENSE_VREF` / `0x07C` `SENSE_CTRL` | sense engine |
| `0x080` | `SOFT_OFFSETS[0..6]` | read-retry / LLR vref offsets (signed i8 codes) |
| `0x090` | `PROG_VSTART` / `0x094` `PROG_VSTEP` / `0x098` `PROG_NPULSE` / `0x09C` `PROG_PV` | ISPP |
| `0x0A0` | `ERASE_MEAN` / `0x0A4` `ERASE_SIGMA` / `0x0A8` `ERASE_EV` | erase model |
| `0x0B0` | `NOISE_SIGMA` / `0x0B4` `WEAR_COEF` / `0x0B8` `RETENTION_COEF` / `0x0BC` `DISTURB_COEF` | physics coefficients |
| `0x0C0` | `FAULT_CTRL` / `0x0C4` `FAULT_TARGET` / `0x0C8` `FAULT_PARAM` | injection |
| `0x0D0` | `PERF[0..7]` | reads, programs, erases, retries, sense cycles, overruns |
| `0x100` | `CELL_WINDOW` | direct 4 KB aperture into the Vt array for debug/checkpoint |

### 6.2 Event record (16 B, ring buffer in core DRAM)

```
struct NandEvent:
    kind:      u8     # CMD | ADDR_DONE | DATA_IN_DONE | RE_BURST_END | TIMING | OOB | RESET
    cmd:       u8     # raw command byte
    flags:     u8     # plane, wp_state, during_busy, illegal_sequence
    seq:       u8     # rolling counter — detects ring overflow
    col:       u16
    row:       u32
    len:       u16    # bytes latched, for DataIn
    timestamp: u32    # emulated ns
```

Ring overflow is a hard error (`EVT_LOST`), not a silent drop: a lost command
event would desynchronize the firmware's FSM from the pin FSM.

---

## 7. Firmware design (Simple, baremetal)

Runtime family `nogc_async_mut_noalloc` — stack only, no allocation, deterministic.

### 7.1 Module layout

```
src/hw/nand_emu/
├── rtl/
│   ├── pin_frontend.spl        # sync, latch, output pre-fetch, Hi-Z
│   ├── timing_check.spl        # AC parameter checker
│   ├── page_buffer.spl         # ping-pong dual-port BRAM
│   ├── accel_sense.spl         # Vt → bit packing
│   ├── accel_program.spl       # ISPP + LFSR noise
│   ├── accel_common.spl        # ADD_DELTA, DIGEST, EDC
│   ├── evt_ring.spl            # event pusher
│   └── nand_emu_top.spl        # SoC-facing wrapper
├── fw/
│   ├── main.spl                # event loop
│   ├── cmd_fsm.spl             # command legality + sequencing
│   ├── geometry.spl            # address decode + shrinking
│   ├── array.spl               # Vt array accessors, metadata
│   ├── physics.spl             # ISPP, erase, disturb, retention, wear
│   ├── badblock.spl            # factory bad-block map generation
│   ├── edc.spl                 # 1 bit/528 B EDC, copy-back status
│   ├── status.spl              # 70h / F1h / 7Bh registers
│   ├── fault.spl               # injection scripts
│   └── trace.spl               # SDN trace emission
├── model/
│   └── golden.spl              # host-side reference model (no HW)
├── test/
│   ├── unit/ ...               # SPipe specs
│   ├── scenario/ ...           # recovery/prevention scenarios
│   └── conformance/ ...        # datasheet timing + command matrix
└── verify/
    └── nand_fsm.lean           # Lean 4 proofs
```

### 7.2 Command FSM

```
# fw/cmd_fsm.spl

enum ChipState:
    Idle
    AddrLatch(cmd: u8, got: i64)
    ReadBusy
    ReadOut
    ProgLoad
    ProgBusy
    EraseSetup
    EraseBusy
    StatusOut(reg: u8)
    IdOut
    CopyLoad
    TwoPlaneStage(stage: i64)
    Undefined              # entered on illegal sequence; only FFh escapes

fn on_command(var st: ChipState, cmd: u8, ctx: var Ctx) -> ChipState:
    if cmd == 0xFF:
        ctx.begin_busy(ctx.reset_time_ns())     # 5 / 10 / 500 µs by prior state
        ctx.status = 0xC0 if ctx.wp_high else 0x40
        return ChipState.Idle

    # Commands legal during busy
    if ctx.busy and cmd != 0x70 and cmd != 0xF1 and cmd != 0x7B:
        ctx.violation(ViolationKind.CmdDuringBusy, cmd)
        return ChipState.Undefined

    match (st, cmd):
        | (ChipState.Idle, 0x00) -> ChipState.AddrLatch(0x00, 0)
        | (ChipState.Idle, 0x80) -> ChipState.AddrLatch(0x80, 0)
        | (ChipState.Idle, 0x60) -> ChipState.EraseSetup
        | (ChipState.Idle, 0x90) -> ChipState.IdOut
        | (ChipState.Idle, 0x70) -> ChipState.StatusOut(0x70)
        | (ChipState.Idle, 0xF1) -> ChipState.StatusOut(0xF1)
        | (ChipState.Idle, 0x7B) -> ChipState.StatusOut(0x7B)
        | _ -> ctx.reject(st, cmd)
```

Rules the FSM enforces (each one is a bug real firmware has shipped):

* Nop ≤ 4 partial programs per page without an intervening erase.
* Pages within a block must be programmed **LSB → MSB**; random page program is
  a violation. This is *prohibited*, not merely discouraged — real chips corrupt.
* Program to an unerased page → data is ANDed (you cannot turn 0 back into 1),
  which the Vt model reproduces naturally, plus a `ProgramWithoutErase` warning.
* Between 11h and 80h/81h/85h only 70h/F1h/FFh.
* Two-plane addressing constraints: A19 fixed low for the first, high for the
  second; A13–A18 fixed low on the first descriptor; same row otherwise.
* WP low → program/erase silently refused, status bit 7 = 0. Enabling WP during
  program/erase busy is prohibited (datasheet Fig. C-1/C-2) → violation event.
* Copy-back only within the same plane.
* Random data input before copy-back: whole-sector, once per sector; anything
  finer **corrupts the on-chip EDC** — the emulator models this by marking the
  sector's EDC validity bit (I/O2 of 7Bh) invalid.

### 7.3 Physics core

```
# fw/physics.spl

struct CellParams:
    erase_mean:   u8      # 88
    erase_sigma:  u8      # 8
    pv_level:     u8      # 148
    ispp_start:   u8      # 130
    ispp_step:    u8      # 6
    ispp_max:     i64     # 20 pulses
    prog_sigma:   u8      # 3
    wear_coef:    f32     # sigma growth per 1000 P/E
    ret_coef:     f32     # Vt loss per decade of seconds, per 1000 P/E
    rd_coef:      f32     # Vt gain per 1000 reads of a neighbor page
    pd_coef:      f32     # Vt gain per program of a neighbor page

fn program_cell(var vt: u8, target_bit: bool, p: CellParams, seed: u32) -> u8:
    if target_bit:            # 1 = leave erased
        vt
    else:
        var v = vt
        var pulse = p.ispp_start
        for _ in 0..p.ispp_max:
            if v >= p.pv_level:
                break
            v = sat_add(v, pulse_delta(pulse, seed) + gauss(p.prog_sigma, seed))
            pulse = sat_add(pulse, p.ispp_step)
        v

fn retention_delta(dt_s: f64, pe_cycles: i64, vt: u8, p: CellParams) -> i32:
    # charge loss ∝ log10(time), worse for high Vt and worn cells
    if vt <= 128: 0
    else:
        mag = p.ret_coef * log10(1.0 + dt_s) * (1.0 + pe_cycles as f64 / 1000.0)
        -(mag * ((vt - 128) as f64 / 40.0)) as i32

fn sense(vt_stored: u8, meta: PageMeta, blk: BlockMeta, vref: u8, now: u64) -> bool:
    eff = clamp_u8(vt_stored as i32
                   + retention_delta(now - meta.last_prog, blk.pe_cycles, vt_stored, P)
                   + disturb_delta(meta.rd_count, meta.pd_count, P))
    eff < vref
```

Note `sense` returns `true` for an erased (=1) bit, and the whole retention /
disturb machinery is applied **at read time** from counters — no array sweep.

### 7.4 Read retry, as the host firmware will use it

```
# The emulator side needs no special support: it just senses at a different vref.
# This is what the DUT firmware running on the host does against the emulator:

RETRY_TABLE: [i8; 7] = [0, -6, +6, -12, +12, -18, +18]

fn read_with_retry(page: u32) -> Result<[u8; 4224], NandError>:
    for k in 0..7:
        set_vref_offset(RETRY_TABLE[k])       # vendor-specific set-feature
        data = read_page(page)
        match ecc_correct(data):
            | Ok(fixed) ->
                if k > 0:
                    mark_for_refresh(page)     # ← prevention logic under test
                return Ok(fixed)
            | Err(_) -> continue
    soft_decision_read(page)                   # ← recovery logic under test
```

The value of the whole project is that this loop **actually behaves differently
at each `k`**, and that `mark_for_refresh` fires on a page whose Vt really has
drifted.

---

## 8. Scenario suite (the deliverable that justifies the build)

Each scenario is an SPipe BDD spec driving the emulator through the fault
interface and asserting on the host firmware's response.

| # | Scenario | Injection | Expected DUT behavior |
|---|---|---|---|
| 1 | Retention failure | `TIME_ADVANCE 1 year` on a block with 30 K P/E | ECC correctable at retry level 2–3, page marked for refresh |
| 2 | Deep retention | 3 years, 80 K P/E | Uncorrectable at level 0, recovered by soft-decision read |
| 3 | Read disturb | 200 K reads of page N | pages N±1 accumulate errors; DUT's read counter triggers block refresh before UECC |
| 4 | Program disturb | Full-block sequential program | neighbor page errors stay within ECC budget; verify no false bad-block retirement |
| 5 | SPO during program | Assert `FAULT_SPO` at pulse 8 of 20 | Partially-programmed page detected on next power-up scan; block rebuilt |
| 6 | SPO during erase | Abort mid-erase | Half-erased block detected; re-erase or retire |
| 7 | Program failure | `FAULT_PROG_FAIL` on page n of block A | status I/O0=1; DUT copies pages 1..n−1 to block B, rewrites page n, marks A invalid — the datasheet's own block-replacement flow |
| 8 | Erase failure | `FAULT_ERASE_FAIL` | block retired, bad-block table updated, table survives power cycle |
| 9 | Factory bad blocks | 40 blocks with non-FFh at column 4,096 of page 0/1 | DUT's initial scan builds the correct table, never erases them |
| 10 | Bad-block info erased | Erase a factory-bad block | detect that the info is unrecoverable — the datasheet warns this is one-way |
| 11 | Wear-out | 100 K P/E on one block | σ growth makes the block fail; wear leveling should have prevented the concentration |
| 12 | Copy-back accumulation | 20 chained copy-backs on a drifted page | 7Bh EDC status reports the error; DUT must not blind-copy |
| 13 | Copy-back EDC invalidation | Sub-sector random data input before copy-back | I/O2 = 0 (invalid); DUT must fall back to read-modify-write |
| 14 | Nop violation | 5th partial program to one page | emulator flags violation; DUT should never reach it |
| 15 | Random page program | program page 5 then page 2 | violation flagged |
| 16 | WP during busy | assert WP mid-program | violation + undefined result, per datasheet prohibition |
| 17 | Timing violation | host with tADL = 60 ns | `EVT_TIMING`; strict mode corrupts the page |
| 18 | Two-plane misaddress | A19 not fixed low on descriptor 1 | violation |
| 19 | Reset during erase | FFh mid-tBERS | busy for tRST(500 µs), block left partially erased, status C0h |
| 20 | Over-erase | erase with soft-program disabled | erased tail below −2.2 V; read margin and GIDL leakage effects visible |

Scenarios 1–3 and 11 are why the Vt byte exists. Scenarios 14–18 are why the
timing checker exists.

---

## 9. Integration as a Simple RV32/RV64 option

### 9.1 Configuration (SDN)

```
# config/soc/rv32_nand_emu.sdn
soc:
    core: rv32imac
    clock_mhz: 100

nand_emu:
    enable: true
    profile: S3                 # S1 | S2 | S3 | S4 | S5
    backing: bram               # bram | sram | ddr3
    timing_mode: model          # realtime | model | dilate
    dilate: 1
    strict_timing: false
    chip_id: [0xEC, 0xD3, 0x10, 0xA6, 0x64]
    oob_policy: alias
    accel_width: 64             # 64 | 128 bits
    dedicated_core: true        # separate RV core vs. shared with SoC

physics |param, value, unit|
    erase_mean, 88, code
    erase_sigma, 8, code
    pv_level, 148, code
    ispp_step, 6, code
    wear_coef, 1.5, code_per_kcycle
    ret_coef, 2.0, code_per_decade
```

### 9.2 Build/test lanes

| Lane | Stack | Purpose |
|---|---|---|
| `nand-emu-model` | host-native Simple, golden model only | fastest iteration; firmware logic |
| `nand-emu-ghdl-s1` | VHDL backend + GHDL, profile S1, mailbox at `0x80FF0000` | RTL correctness, protocol conformance |
| `nand-emu-ghdl-s2` | same, S2 | sector/EDC semantics |
| `nand-emu-qemu` | RV32 firmware in QEMU + model | firmware regression without RTL |
| `nand-emu-fpga-s3` | real bitstream, host controller on the pins | timing closure, real-world validation |

Add these to `doc/08_tracking/lane_matrix.md` with honest status labels — this
project should follow the repo's existing discipline of `stable` /
`host-aware` / `unsupported` rather than blanket claims.

### 9.3 Lean 4 verification targets

The command FSM is small, total, and worth proving:

1. **Reachability**: from any state, `FFh` reaches `Idle` (reset always works).
2. **No silent corruption**: every transition either advances a legal datasheet
   sequence or emits a violation event — no third option.
3. **Erase-before-program**: programming a page whose block has not been erased
   since the last program can only clear bits, never set them (monotonicity of
   the Vt model under `program`).
4. **Nop bound**: the partial-program counter never exceeds 4 without an
   intervening erase.
5. **Address bijectivity**: for `OOB_POLICY = WINDOW`, `(col, row) →
   cell_index` is injective within the window (no aliasing bugs in the shrink).
6. **Additivity/commutativity of drift**: lazy application yields the same
   result as eager application — this is the correctness proof of §3.4, and it
   is the one most likely to catch a real bug.

### 9.4 Public API for the host side

```
import hw.nand_emu

emu = NandEmu.attach(base: NAND_EMU_BASE)
emu.load_profile(Profile.S3)
emu.set_factory_bad_blocks(count: 40, seed: 0xC0FFEE)
emu.set_time_dilation(1)

# fault injection from a test
emu.inject(Fault.SuddenPowerOff(during: Op.Program, at_pulse: 8))
emu.advance_time(days: 365)
emu.disturb(page: 1024, reads: 200_000)

# introspection — impossible on real silicon, the reason to build this
hist = emu.vt_histogram(page: 1024)         # 256-bin distribution
emu.dump_vt(page: 1024, path: "vt_1024.sdn")
margin = emu.read_margin(page: 1024)        # valley width between the two lobes
```

`vt_histogram` and `read_margin` are the observability payoff: you can watch the
two distributions merge as retention or wear progresses, and correlate that
directly with the moment your firmware's ECC gives up.

---

## 10. Implementation plan

| Phase | Deliverable | Exit criterion | Est. |
|---|---|---|---|
| **P0** Spec & golden model | Datasheet-derived spec doc, `model/golden.spl`, command matrix table | golden model passes a hand-written trace of all 18 command sequences | 1 wk |
| **P1** Pin frontend RTL | `pin_frontend.spl` → VHDL, GHDL testbench driving real waveforms | latch classification and column counter correct incl. CE don't-care; GHDL lane green | 1.5 wk |
| **P2** Timing checker | `timing_check.spl`, violation events | every AC parameter in §1.6 measured; deliberate violations detected | 0.5 wk |
| **P3** Event ring + firmware skeleton | `evt_ring.spl`, `fw/main.spl`, `cmd_fsm.spl` | Read ID (90h), Reset (FFh), Read Status (70h) work end-to-end in GHDL | 1 wk |
| **P4** Read path | page buffer, `accel_sense.spl`, `array.spl`, geometry shrink | 00h/30h returns correct data from a pre-filled Vt array within tR (MODEL mode) | 1.5 wk |
| **P5** Program + erase | `accel_program.spl`, ISPP, 80h/10h, 60h/D0h | program/erase round-trip; unerased-program ANDs correctly; Nop enforced | 1.5 wk |
| **P6** Full command set | random data in/out, copy-back, EDC, two-plane, 2 KB compat, F1h/7Bh | full command matrix passes conformance suite | 2 wk |
| **P7** Physics | `physics.spl`: disturb, retention, wear, lazy drift + Lean proof #6 | scenarios 1–4, 11 reproduce expected failure onsets | 2 wk |
| **P8** Fault injection + scenarios | `fault.spl`, scenario suite 1–20 | all 20 scenarios run in CI on profile S3 | 1.5 wk |
| **P9** FPGA bring-up | constraints, IOB placement, level shifters, TSOP1 adapter, DDR3 for S4 | real host controller enumerates the chip and passes an FTL mount/format/verify | 2 wk |
| **P10** Integration | SDN config option, lane matrix entries, docs, Lean proofs 1–5 | `soc.nand_emu.enable: true` builds RV32 and RV64 SoCs; docs merged | 1 wk |

**Total ≈ 15–16 weeks** at one engineer. P0–P5 (≈7 wk) already gives a usable
read/program/erase emulator; P7–P8 is where the recovery/prevention value lands.

### 10.1 Risk register

| Risk | Impact | Mitigation |
|---|---|---|
| `tREA ≤ 20 ns` not met on target FPGA | host reads garbage | output pre-fetch into IOB FF (§5.1); document a minimum-tRC constraint; fall back to a slower host clock |
| Sense throughput < tR | overrun in REALTIME | 200 MHz accel clock or 128-bit path; MODEL mode as escape hatch |
| DDR3 latency jitter on S4/S5 | nondeterministic timing | prefetch whole page into BRAM at command latch; DDR only on page granularity |
| VHDL backend subset gaps | RTL won't compile | P1 is deliberately first and small — it is the real feasibility test; check `vhdl_support_matrix.md` before writing, expect fail-fast diagnostics |
| Event ring overflow | firmware/pin FSM desync | ring sized for worst-case burst; overflow is a hard error with a dedicated IRQ |
| Physics model plausible but wrong | firmware tuned to fiction | calibrate coefficients against published NAND characterization data; keep all coefficients as registers, never constants; document the model as *phenomenological, not device-physical* |
| 3.3 V pins vs 1.8 V FPGA bank | hardware damage | level shifters on the adapter board; verify before power-on |

### 10.2 Honest scope limits (state these in the README)

* This is a **phenomenological** model, not TCAD. Vt deltas are fitted curves,
  not solved physics. It reproduces the *shape* of failures, not the exact
  numbers of any particular process node.
* SLC only in v1. MLC/TLC needs 4/8 distributions and page-type mapping
  (LSB/CSB/MSB), which changes the program model substantially — designed for,
  not implemented.
* Two-plane is emulated functionally; the timing overlap is approximated.
* Cell-to-cell coupling (Vt of a neighbor affecting the sensed Vt of this cell)
  is *not* in v1. It is the most significant missing effect and the natural v2
  item, since it drives much of real MLC read-retry behavior.
* Profile `S6` (full geometry with Vt bytes, 8.86 GB) is documented as
  unbuildable rather than quietly omitted.

---

## 11. First week, concretely

1. `doc/05_design/nand_emu.md` — this document, committed, with the datasheet
   table extracted into SDN so tests can consume it.
2. `test/conformance/nand_command_matrix.sdn` — named table of all command
   sequences, each with legality preconditions and expected busy time.
3. `model/golden.spl` — pure-Simple reference: command FSM + bit array (no Vt
   yet), runs on host, ~800 lines.
4. `test/unit/cmd_fsm_spec.spl` — SPipe spec driving the golden model through
   the matrix; this becomes the regression oracle for the RTL later.
5. A one-page feasibility spike: write `pin_frontend.spl`, run it through the
   VHDL backend, and see what the fail-fast diagnostics say. **Do this in week
   one** — it determines whether the whole RTL-in-Simple premise holds, and it
   is cheap to find out.

---

## Appendix A — Vt array memory layout

```
cell_index(row, col, bit) = ((row * page_bytes) + col) * 8 + bit
vt_addr                   = VT_BASE + cell_index

page_meta[row]  : 16 B  { last_prog_time:u64, rd_count:u32, pd_count:u16,
                          nop_count:u8, flags:u8 }
block_meta[blk] : 16 B  { pe_cycles:u32, last_erase_time:u64,
                          bad_flag:u8, edc_state:u8, reserved:u16 }
```

Meta arrays live in a separate region so a `DIGEST` over the Vt array is
contiguous, and so a checkpoint can save meta alone (small) for fast scenario
setup.

## Appendix B — Suggested default physics coefficients

| Coefficient | Default | Meaning |
|---|---|---|
| `erase_mean / sigma` | 88 / 8 | erased lobe, −1.00 V ± 0.20 V |
| `pv_level` | 148 | program verify, +0.50 V |
| `ispp_start / step` | 130 / 6 | first pulse and increment (codes) |
| `ispp_max` | 20 | pulses before program failure |
| `prog_sigma` | 3 | per-pulse randomness |
| `wear_coef` | +1.5 code σ per 1,000 P/E | distribution widening |
| `ret_coef` | 2.0 codes per decade of seconds at 1 K P/E | charge loss |
| `rd_coef` | +1 code per 10,000 neighbor reads | read disturb |
| `pd_coef` | +1 code per 200 neighbor programs | program disturb |
| `erase_floor_coef` | +0.8 code per 1,000 P/E | erased lobe rises with wear |

With these, a block at 30 K P/E held for one emulated year shows roughly a
15-code downward shift of the programmed lobe — enough to push the weak tail
across `vref = 128` and produce a handful of correctable errors per 528 B sector.
That is the intended calibration target: **failures should appear at a rate that
exercises ECC and refresh, not at a rate that makes every read fail.**
