# Workstream G — The Hardware IR Single-Source Layer

**Parent:** `doc/03_plan/hardware/nvme_complete_fw_mdsoc_offload_master_plan.md` §11.4 (row G).
**Research sources:** `simpleemu_unified_emulator_nvme_riscv_test_infra_plan.md` §7 (7.1 RegisterIR,
7.2 `@reg` surface, 7.3 AOP/EffectIR, 7.4 PinIR/PadIR, 7.5 ProtocolIR);
`nvme_ssd_firmware_hardening_design_plan.md` §6.4 (SystemRDL / IEEE 1685 IP-XACT / CMSIS-SVD survey).
**Scope:** RegisterIR, PinIR/PadIR, MemoryIR, ProtocolIR, EffectIR — one definition per hardware
fact, every downstream view generated, none hand-edited.

**Status: PLAN ONLY. Nothing in this document is implemented.** Every "generated" artifact below
is a target. Existence claims about the current tree are cited `file:line`; everything else is
marked *(inferred)* or *(illustrative)*.

---

## 1. Measured starting position

### 1.1 There is no register, pin, protocol, or memory IR in this repo

A whole-tree scan for the IR names in this workstream returns **zero** `.spl` files:

```
grep -rln 'RegisterIR|PinIR|ProtocolIR|MemoryIR|SystemRDL|IP-XACT|cmsis-svd' src/ --include=*.spl
  -> (no output)
```

A scan for a generic register-map abstraction (`sfr`, `register_map`, `RegisterMap`, `RegBlock`)
returns 3 files, and all three are incidental substring hits with no register semantics:
`src/lib/hardware/rv64gc_rtl/fpu.spl`, `src/lib/common/web/public_suffix_data.spl`,
`src/lib/gc_async_mut/gpu/browser_engine/html_named_character_references.spl`.

**Conclusion (measured): this layer is greenfield.** There is no schema to extend, no importer to
reuse, and no existing generator whose output could be diffed. That is a cost, but it is also the
one favourable fact in this workstream — G is not blocked behind a migration.

### 1.2 There is a real HWIR, and it cannot host RegisterIR or MemoryIR today

`src/compiler/50.mir/hwir/` is a substantial, live subsystem: 44 files including
`types.spl` (657 lines), `mir_to_hwir.spl` (727 lines), `host_evaluator.spl` (279 lines), a
`sequential.spl`, and a large RISC-V scalar-core projection family. A VHDL backend consumes it
(`src/compiler/70.backend/backend/vhdl_backend.spl` and siblings), with a compile-time constraint
checker at `src/compiler/70.backend/vhdl_constraints.spl:1-30` that already models width, clock
domain, CDC, sensitivity-completeness and comb-loop constraints.

The constraint carried forward from **workstream A**, re-verified here:

| Constraint | Cite | Consequence for G |
|---|---|---|
| A strict module may not claim registers or memories | `src/compiler/50.mir/hwir/types.spl:528-529` — `HWIR-E-MODULE-STATE: combinational module definition cannot claim unrepresented state or memories`, guarded by `summary.register_count != 0 or summary.memory_count != 0` | **RegisterIR and MemoryIR are not HWIR features.** They are a separate IR that HWIR will *later* consume, not an HWIR extension |
| Strict MIR lowering rejects clocked functions | `src/compiler/50.mir/hwir/mir_to_hwir.spl:588` — `HWIR-E-CLOCKED: strict MIR lowering currently supports combinational functions only` | A generated RTL register bank cannot be lowered through strict HWIR at all; G's RTL emitters emit **text** (VHDL/SV source), not HWIR nodes, until A lands a clocked tier |

This is the single most important design consequence in this plan and it is why §3 makes the
generators text emitters rather than HWIR builders. Anyone who tries to make RegisterIR "just an
HWIR node kind" will hit `types.spl:528` on the first register.

### 1.3 The drift this layer exists to stop is already measurable

The Cosmos+ OpenSSD port is the concrete case. The NFC aperture base `0x43C00000` is
**independently hand-written in 7 files across 3 languages**:

| File | Form |
|---|---|
| `src/os/kernel/arch/arm32/platform/cosmos_openssd.spl:19` | `val COSMOS_NFC_PL_BASE: u64 = 0x43C00000` |
| `src/os/kernel/arch/arm32/cosmos/cosmos_nfc_regs.h:24` | `#define COSMOS_NFC_CHANNEL0_BASE 0x43C00000U` |
| `src/os/kernel/arch/arm32/cosmos/cosmos_hal.h` | aperture constant |
| `src/os/kernel/arch/arm32/cosmos/cosmos_mmu_cache.c` | MMU mapping literal |
| `examples/09_embedded/simpleos_nvme_fw/fw/openssd_config.spl` | config literal |
| `examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_target_core.spl` | target aperture |
| `examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_target_aperture_cases.spl` | test cases |

14 total occurrences. The PCIe aperture `0x83C00000` is likewise duplicated across
`cosmos_pcie_regs.h:34`, `cosmos_pcie.c`, `cosmos_hal.h`, and `cosmos_mmu_cache.c`.

The register *offsets* are equally hand-maintained: `cosmos_nfc_regs.h:29-35` is a flat block of
`#define`s (`COSMOS_NFC_CMD_SELECT 0x00U`, `ROW_ADDRESS 0x04U`, `USER_DATA 0x08U`,
`DATA_ADDRESS 0x0CU`, `SPARE_ADDRESS 0x10U`, `ERROR_COUNT_ADDRESS 0x14U`,
`COMPLETION_ADDRESS 0x18U`), and `cosmos_pcie_regs.h:38-52` the same for PCIe
(`CONTROL 0x0000`, `IRQ_MASK 0x0004`, `IRQ_CLEAR 0x0008`, `IRQ_STATUS 0x000C`, `STATUS 0x0100`,
`FUNCTION 0x0104`, `NVME_STATUS 0x0200`, `HOST_DMA_FIFO_COUNT 0x0204`, `ADMIN_QUEUE 0x021C`,
`IO_SQ 0x0220`, `IO_CQ 0x0260`, `NVME_CMD_FIFO 0x0300`, `NVME_CPL_FIFO 0x0304`,
`HOST_DMA_CMD_FIFO 0x0310`, `NVME_CMD_SRAM 0x2000`).

There are **210 lines of `cosmos_nfc_regs.h` and 270 of `cosmos_pcie_regs.h`** with no generator,
no schema, and no cross-check against the `.spl` copies. Nothing in the tree fails when they
diverge. Note also that these headers are C — the `no new rt_*` / "impl in Simple" direction makes
them a migration target independent of G, and G is the mechanism that migrates them.

### 1.4 What already exists that G plugs into

- **VHDL emission and constraint checking** — `vhdl_backend.spl`, `vhdl_constraints.spl`. PinIR's
  top-level port list and clock-domain facts are the natural input to the existing
  `SameClockDomain` / `ClockDomainCrossing` constraints (`vhdl_constraints.spl:24-30`). *(inferred:
  the wiring does not exist; only the constraint vocabulary does.)*
- **HWIR host evaluator** — `host_evaluator.spl` (279 lines) is the SW-side oracle workstream A's
  equivalence gate uses. G's ProtocolIR checkers should emit into the same observation shape so one
  comparison harness serves both. *(inferred.)*
- **SDN as the config format** — nested `simple.sdn` style, e.g. `src/lib/simple.sdn:4-16`
  (`project:` / `name:` / `dependencies:` with `- project:` list items). G's schema follows it.

---

## 2. The five IRs

One SDN file family, one schema, five top-level sections. **Deliberately one compact schema, not a
framework** — no plugin registry, no dynamic type system, no user-extensible field kinds. If a
concept is not needed by a named consumer in §5 it is not in the schema.

Proposed location: `src/hardware/ir/` for the schema readers and generators (pure Simple),
`spec/hw/<device>/*.sdn` for the definitions themselves, `generated/` for output.

### 2.1 RegisterIR

Per SimpleEMU §7.1. Three levels: block, register, field.

```sdn
register_block:
  id: cosmos_nfc
  name: "Cosmos+ NAND flash controller"
  bus: axi_gp0
  endian: little
  base: 0x43C00000
  size: 0x00010000
  array:
    dim: channel
    count: 8
    stride: 0x00010000
  clock_domain: pl_clk0
  reset_domain: pl_reset_n
  security_domain: firmware_privileged

  register:
    - id: cmd_select
      offset: 0x00
      width: 32
      reset: 0x00000000
      access: wo
      field:
        - id: uprogrom_entry
          bits: "7:0"
          semantic: uprogrom_index
          access: wo
          on_write: start_sequence
          reserved: rsvd_zero
```

Access policies (closed set, from §7.1): `ro | wo | rw | w1c | w0c | rc | rs | self_clear |
shadowed | pulse | fifo_port | counter | latch_on_event | implementation_defined`.

Per-field attributes: `bits`, `semantic` (a named type, not a raw width), `access`,
`reserved` (`rsvd_zero` | `rsvd_preserve` | `rsvd_ignore`), `on_write` / `on_read` side effect,
`self_clear_latency`, `irq` relation, `privilege`, `volatile`, `atomic`, `test_visible`.

Banking is the `array:` block (dim/count/stride), and it composes: a register may itself carry an
`array:` for a repeated window (`io_sq` at `0x0220`, `io_cq` at `0x0260` in the real PCIe header
are exactly this shape).

**Side effects are first-class, not comments.** `on_write: start_sequence` is what makes the
generated firmware accessor non-reorderable, what makes the emulator dispatch fire an event, and
what makes the AOP effect fact `effect(RegWrite<cosmos_nfc.cmd_select>)` exist. A register model
that records only offsets and widths (which is what `cosmos_nfc_regs.h` is) cannot generate any of
those three, and that is the concrete reason SVD-shaped models are insufficient here.

### 2.2 PinIR / PadIR

Per SimpleEMU §7.4, three record kinds kept separate so board facts never contaminate silicon facts:

```sdn
pad:
  - id: nand_ch0_dq0
    function: nfc_dq
    package_ball: "AA13"
    bank: 34
    voltage: 1.8
    direction: bidir
    pull: none
    drive: 8
    slew: fast
    schmitt: false
    open_drain: false
    differential_mate: none
    clock_domain: pl_clk0
    reset_domain: pl_reset_n
    power_domain: vccio_34
    safe_reset_value: z
    test_mode_owner: boundary_scan

pin_mux:
  - pad: nand_ch0_dq0
    legal_function: [nfc_dq, gpio, jtag_tdi]
    mux_sfr: cosmos_nfc.pinmux_ch0
    mux_field: dq0_sel
    boot_strap: none
    conflict: [jtag_tdi excludes nfc_dq]

board_connection:
  - pad: nand_ch0_dq0
    connector: "J7.14"
    net: "NAND_CH0_DQ0"
    external_device: nand_ch0_pkg
    direction: bidir
    level: lvcmos18
    constraint: { max_skew_ps: 50 }
```

The `pin_mux.mux_sfr` field is the join to RegisterIR: a mux SFR must resolve to a real
`register_block.register.field`, and a gate enforces that (§6, G-IR-3).

### 2.3 MemoryIR

Needed by **workstream F** for MBIST generation (master plan §11.3, "MBIST from MemoryIR"). Kept
minimal: only what an MBIST wrapper generator and a linker fragment need.

```sdn
memory:
  - id: nvme_cmd_sram
    kind: sram_sp
    words: 2048
    width: 32
    banks: 1
    base: 0x43C02000        # cosmos_pcie_regs.h:52 NVME_CMD_SRAM_OFFSET, +block base
    ecc: none
    redundancy: none
    clock_domain: pl_clk0
    reset_domain: pl_reset_n
    bist:
      algorithm: march_c_minus
      wrapper: ieee1500
      repair: none
    access: [firmware_privileged, dma_engine]
```

MemoryIR is **not** a way to smuggle memories into HWIR — `types.spl:528-529` still rejects them.
It describes memories for MBIST, linker fragments, emulator backing stores, and the access manifest.

### 2.4 ProtocolIR

Per SimpleEMU §7.5. One transaction vocabulary, one checker per protocol, four possible observation
levels (semantic transaction / register / pin / RTL signal) all emitting the same observation record
so a comparison harness does not care which level produced it.

```sdn
protocol:
  - id: nvme
    layer: semantic
    transaction:
      - id: nvme_sqe
        fields: [opc, fuse, psdt, cid, nsid, mptr, prp1, prp2, cdw10..cdw15]
        encoding: le64_le32
      - id: nvme_cqe
        fields: [dw0, sq_head, sq_id, cid, phase, status]
      - id: prp_list
        rule: "prp2 is a list pointer when transfer crosses > 2 pages"
    checker: [phase_tag_alternates, cid_unique_in_flight, prp_page_aligned]
```

Required coverage (§7.5): PCIe TLP + endpoint events; NVMe registers/commands/queue
entries/completions/PRP+SGL descriptors; AXI/APB/Wishbone; ONFI/Toggle command/address/data/status
cycles; JTAG/DMI/IJTAG; UART/SPI/I2C/GPIO/timers/interrupt controllers.

The NVMe half of ProtocolIR is where **workstream D**'s register and command decode comes from —
D should not write a second decoder.

### 2.5 EffectIR

Named in master plan §11.4 as part of G, defined in SimpleEMU §7.3. EffectIR is not a separate file
format: it is the **derived** projection of the other four. Every RegisterIR field with an
`on_write`/`on_read`, every PadIR drive, every MemoryIR access entry, and every ProtocolIR
transaction contributes one effect fact:

```
effect(RegRead) effect(RegWrite) effect(DmaRead) effect(DmaWrite)
effect(RaiseIrq) effect(ScheduleEvent) effect(NandProgram) effect(PinDrive)
```

Generated as AOP policy facts so §7.3's declarative rules become checkable:

```
forbid  FTL -> effect(RegWrite<cosmos_nfc.*>)
forbid  firmware -> effect(TestControl.*)
allow   FIL.media_driver -> effect(RegWrite<cosmos_nfc.*>)
forbid  speculative_path -> effect(RegRead<SideEffecting.*>)
```

Because EffectIR is derived, it cannot drift from RegisterIR by construction — there is no second
place to edit it. *(Compiler work: first-class `effect(...)` selectors do not exist today; §7.3
notes the interim uses `attr(reg)` + `within`/`execution` selectors. Staged in §7.)*

---

## 3. The generator contract

### 3.1 Artifacts per IR

| IR | Generated artifact | Consumer |
|---|---|---|
| RegisterIR | typed Simple firmware accessors | firmware (D, H) |
| RegisterIR | C header (replaces `cosmos_nfc_regs.h`, `cosmos_pcie_regs.h`) | legacy C HAL, until migrated |
| RegisterIR | native behavioral register bank | emulator (E) |
| RegisterIR | SimpleEMU MMIO table + fast dispatch ids | emulator (E) |
| RegisterIR | VHDL/SystemVerilog register block **as text** | RTL (A, once a clocked tier exists) |
| RegisterIR | UVM RAL adapter data | external verification |
| RegisterIR | debugger register metadata | debug (F) |
| RegisterIR | SSpec field selectors, masks, reset + negative tests | test (F/SVAP) |
| RegisterIR | AOP policy facts (EffectIR) | verification (C, H) |
| RegisterIR | register documentation | docs |
| RegisterIR | SystemRDL / IP-XACT / SVD export | external tools (§4) |
| PinIR/PadIR | RTL top-level ports + pad-ring wrapper | RTL |
| PinIR/PadIR | FPGA XDC / SDC / PCF constraints | FPGA lane |
| PinIR/PadIR | board connection table | board bring-up |
| PinIR/PadIR | BSDL skeleton / input data | DFT (F) |
| PinIR/PadIR | pin-mux firmware accessors | firmware |
| PinIR/PadIR | boundary-scan + board-loopback test intent | DFT (F) |
| PinIR/PadIR | **ATE functional pin groups and timing-set input** | ATE (F) — see §3.4 |
| PinIR/PadIR | docs / schematic consistency report | docs |
| MemoryIR | MBIST wrapper + algorithm config | DFT (F) |
| MemoryIR | linker fragments | firmware build |
| MemoryIR | emulator backing-store table | emulator (E) |
| MemoryIR | access-manifest rows | AOP (H) |
| ProtocolIR | typed transaction records + encoders/decoders | D, E |
| ProtocolIR | shared protocol checkers | E, F |
| ProtocolIR | testbench constants + conformance vectors | verification |
| EffectIR | AOP policy fact set | C, H |

### 3.2 The never-hand-edit rule, enforced mechanically

Hardening plan §6.4 states it: *"Generated files are never hand edited. CI regenerates them and
fails on differences."* A comment header is not enforcement. The mechanism:

1. Every generated file begins with a machine-readable provenance header carrying the generator id,
   the schema version, and the **content hash of the source `.sdn`**.
2. `scripts/check/check-hw-ir-generated-current.shs` regenerates every artifact into a scratch tree
   and runs `diff -r` against the committed tree. Any difference is a FAIL, naming each file.
3. The gate is **fail-closed on non-vacuity**: a run that regenerated 0 artifacts is ERROR, exit 2,
   never PASS (repo convention, `.claude/rules/vcs.md`).
4. Generators are **deterministic**: sorted iteration order, no timestamps, no host paths, no
   map-iteration order dependence. A generator that emits a timestamp makes the diff gate useless
   and must fail its own selftest.

The rule has teeth only if the diff gate exists *before* the first generated file lands. Sequence
matters: gate first, then generate.

### 3.3 Worked example — one real register, every view

**Source of truth (real values, `cosmos_nfc_regs.h:24-35`; the field breakdown of `cmd_select` and
all bit ranges below are *illustrative* — the upstream uProgROM entry encoding is not recorded in
this repo).**

`spec/hw/cosmos/nfc.sdn`:

```sdn
register_block:
  id: cosmos_nfc
  base: 0x43C00000          # REAL — cosmos_nfc_regs.h:24, cosmos_openssd.spl:19
  size: 0x00010000          # REAL — CHANNEL_STRIDE, cosmos_nfc_regs.h:25
  array: { dim: channel, count: 8, stride: 0x00010000 }   # REAL — CHANNEL_COUNT :26
  bus: axi_gp0
  clock_domain: pl_clk0
  register:
    - id: cmd_select        # REAL offset 0x00 — cosmos_nfc_regs.h:29
      offset: 0x00
      width: 32
      reset: 0x00000000     # ILLUSTRATIVE
      access: wo
      field:
        - { id: uprogrom_entry, bits: "7:0", access: wo, on_write: start_sequence }  # ILLUSTRATIVE bits
        - { id: way_select,     bits: "10:8", access: wo }                            # ILLUSTRATIVE
        - { id: rsvd,           bits: "31:11", reserved: rsvd_zero }                  # ILLUSTRATIVE
    - id: row_address        # REAL offset 0x04 — :30
      offset: 0x04
      width: 32
      access: rw
    - id: error_count        # REAL offset 0x14 — :34
      offset: 0x14
      width: 32
      access: ro
      field:
        - { id: corrected_bits, bits: "15:0", access: ro, semantic: ecc_corrected_count }  # ILLUSTRATIVE
    - id: completion         # REAL offset 0x18 — :35
      offset: 0x18
      width: 32
      access: w1c
      field:
        - { id: done, bits: "0:0", access: w1c, irq: nfc_done_irq }   # ILLUSTRATIVE
```

Generated views from that one block (all *illustrative renderings* of a generator that does not
exist yet):

**(a) Typed Simple firmware accessor** —
```simple
# GENERATED from spec/hw/cosmos/nfc.sdn (sha256 <hash>) — DO NOT EDIT
fn nfc_cmd_select_write(ch: ChannelIndex, entry: UProgRomEntry, way: WayIndex) -> ():
    # effect(RegWrite<cosmos_nfc.cmd_select>), effect(NandProgram)
    reg_write32(COSMOS_NFC_BASE + ch.stride(), 0x00, entry.bits() | (way.bits() << 8))
```

**(b) C header** — regenerates `cosmos_nfc_regs.h:24-35` verbatim, retiring the hand-written copy.

**(c) SimpleEMU MMIO row** — `{ base 0x43C00000, stride 0x10000, count 8, off 0x00, w 32, wo,
dispatch NFC_CMD_SELECT, effect start_sequence }`.

**(d) VHDL register-block text** — a `cosmos_nfc_regs` entity with `cmd_select_q` write-only
strobe, `completion_done_q` W1C bit, and an `error_count_i` read-only input port. **Emitted as
text, not as HWIR nodes** — `types.spl:528-529` forbids a strict module claiming registers.

**(e) SSpec test content** — reset-value test on `row_address`; write-1-clear test on
`completion.done` (write 1 -> reads 0; write 0 -> unchanged); negative test that a write to
`error_count` (RO) is ignored; a reserved-field test that writing 1 to `cmd_select[31:11]` is
rejected.

**(f) AOP / EffectIR facts** — `allow FIL.media_driver -> effect(RegWrite<cosmos_nfc.cmd_select>)`;
`forbid FTL -> effect(RegWrite<cosmos_nfc.*>)`;
`forbid speculative_path -> effect(RegWrite<cosmos_nfc.cmd_select>)` (it has `on_write`).

**(g) Debugger metadata** — 8 channel instances x 7 registers with names, widths, access, and
`error_count.corrected_bits` decoded as a count.

**(h) Documentation** — a register table with offsets, reset values, access, and field descriptions,
plus a cross-reference showing the 7 files that currently duplicate the base address so the
migration is auditable.

**(i) Export** — SVD peripheral (lossless for this block); SystemRDL `regfile` with `w1c` onwrite
(lossless); IP-XACT `memoryMap` (lossy — `on_write: start_sequence` has no standard home; see §4).

**Pad worked example** — a PCIe-side pad from the same board. `10EE:7028`, class `010802`, BAR0
8 KiB (**REAL** — `cosmos_openssd_port_2026-06-30.md:49`) become PinIR/ProtocolIR identity facts;
the PCIe host aperture `0x83C00000` span `0x10000` with `status 0x0100`, `function 0x0104`,
`nvme_status 0x0200`, `admin_queue 0x021C`, `io_sq 0x0220`, `io_cq 0x0260` (**REAL** —
`cosmos_pcie_regs.h:34-48`) become a second `register_block`, from which the PCIe endpoint's
top-level ports, its XDC bank/voltage constraints, and its ATE pin group are generated. Ball
numbers, banks and voltages are **not recorded anywhere in this repo** and would be invented —
they are therefore omitted here rather than fabricated, and the first real PadIR must be
transcribed from the board's XDC.

### 3.4 The ATPG honesty boundary (non-negotiable)

Master plan §11.3 / EMU invariant 8: functional vectors project across simulation, FPGA, board and
ATE, but **Simple does not generate manufacturing test patterns.** PinIR feeds ATE functional pin
groups and timing-set *input*; scan stuck-at/transition ATPG comes from an external tool run on a
scan-inserted netlist. Simple may **configure, package, schedule, compare, and trace** those
patterns. No gate name, doc line, or capability bit in this workstream may say or imply otherwise.
The gate names in §6 are chosen accordingly (`check-hw-ir-ate-pin-groups` — not "ate-patterns").

---

## 4. Import / export adapters

Hardening plan §6.4 concluded that SystemRDL, IEEE 1685 IP-XACT and CMSIS-SVD each demonstrate the
one-source value but none alone covers SSD profile semantics. The adapters are therefore
**asymmetric by design**: import is a bootstrap convenience, export is a compatibility surface, and
the native schema is authoritative in both directions.

| Direction | Round-trips | Lossy in | Why |
|---|---|---|---|
| SVD -> RegisterIR | offsets, widths, reset, access, field bits, arrays (`dimIncrement`) | — | SVD is a subset of RegisterIR |
| RegisterIR -> SVD | the same subset | side effects, `pulse`/`fifo_port`/`latch_on_event`, self-clear latency, privilege, test visibility, clock/security domain | SVD has no vocabulary for them |
| SystemRDL -> RegisterIR | offsets, widths, reset, `onwrite`/`onread` (incl. `woclr`/`woset`), arrays, regfile nesting | RDL component parameters, RDL-side generate expressions | our schema is data, not a parameterized language |
| RegisterIR -> SystemRDL | most of the above | security domain, ATE test visibility, NAND/media profile links | outside RDL's model |
| IP-XACT -> RegisterIR | memory maps, address blocks, registers, fields, access | bus interface / component wiring beyond registers | we import registers only |
| RegisterIR -> IP-XACT | registers/fields | side effects, domains, media semantics | no standard home |
| **Anything -> PinIR/PadIR/MemoryIR/ProtocolIR** | **nothing** | all | none of the three standards models pads, MBIST, or transactions |

**Lossy directions must fail loudly.** The rule:

- An **export** that would drop a semantic the native schema carries emits a
  `HWIR-IR-E-EXPORT-LOSSY` diagnostic naming every dropped attribute and **fails by default**.
  `--allow-lossy-export` is required to proceed, and it **records the dropped set in the output
  file's provenance header** — so a downstream reader can see what is missing. There is no silent
  drop and no env var that disables the record.
- An **import** that meets a construct the native schema cannot represent fails with
  `HWIR-IR-E-IMPORT-UNREPRESENTABLE` and names it. Importing 90% of a register map and saying
  nothing is the exact failure mode this workstream exists to prevent.
- **Import is one-shot, not a live dependency.** An imported `.sdn` is committed and becomes the
  source of truth; the original SVD/RDL/IP-XACT file is recorded in provenance and never re-read at
  build time. Two live sources is two sources.

---

## 5. Consumers and critical-path position

| Workstream | Depends on | For |
|---|---|---|
| **F** (RISC-V production/debug/DFT + SVAP) | PinIR/PadIR | ATE functional pin groups + timing-set input; BSDL skeletons; boundary-scan intent |
| **F** | MemoryIR | MBIST wrapper + algorithm config (master plan §11.3 names MemoryIR as the source) |
| **F** | RegisterIR | debugger register metadata; SSpec field selectors/masks/reset+negative tests |
| **C** (controller/media profile portability) | RegisterIR + MemoryIR | profile generators; the §6.4 "typed accessors, RTL packages, headers, linker fragments, AOP facts, testbench constants, docs, conformance vectors from one source" list |
| **D** (NVMe hardening) | ProtocolIR | NVMe register/command/queue/PRP-SGL decode — D must not write a second decoder |
| **E** (emulator + scheduling) | RegisterIR, MemoryIR, ProtocolIR | MMIO tables, fast dispatch ids, backing stores, shared checkers |
| **H** (typed firmware model, arenas) | EffectIR + MemoryIR | access manifest, AOP policy facts |
| **A** (offload HW/SW partition) | RegisterIR, MemoryIR | *reverse dependency* — A's future clocked/memory HWIR tier is what finally lets RegisterIR/MemoryIR lower to HWIR instead of to text |

**Critical path.** Master plan §11.3 states G6 is unreachable without §11 SVAP and §7.4
PinIR/PadIR. So:

```
G (RegisterIR, PinIR, MemoryIR, ProtocolIR)  ->  F (SVAP + DFT projections)  ->  G6
```

G is **upstream of F and therefore of G6**, and F cannot start its ATE/MBIST/BSDL projection work
before G's PinIR and MemoryIR schemas are frozen. G is also upstream of C and D, which can proceed
on hand-written definitions in the interim but will need to migrate. G is *not* blocked by A — the
text-emitter design in §1.2 is precisely what removes that dependency. **G should start first among
the added workstreams.**

---

## 6. Gates

Repo verdict convention (`.claude/rules/vcs.md`): last line of stdout is
`PASS — <n> ... checked, ...` exit 0 / `FAIL — ...` exit 1 / `ERROR — nothing was checked` exit 2.
A run that checked 0 things is **ERROR, never PASS**. `--selftest` runs first, unconditionally, and
is fatal. **Every gate below ships with a sabotage fixture proving it turns red** — a gate whose red
path was never exercised is not evidence.

| Gate | Checks | Sabotage that must turn it red |
|---|---|---|
| `check-hw-ir-schema-valid.shs` | every `spec/hw/**/*.sdn` parses; access policies are in the closed set; field bit ranges are in-range, non-overlapping, and cover the width or are explicitly reserved; every register offset is within `block.size`; no duplicate ids | add a field `bits: "34:32"` to a 32-bit register; add `access: rw_maybe` |
| `check-hw-ir-generated-current.shs` | regenerate all artifacts to a scratch tree, `diff -r` vs committed; provenance hashes match their `.sdn` | hand-edit one byte of a generated accessor; bump an `.sdn` offset without regenerating |
| `check-hw-ir-crossref.shs` | every `pin_mux.mux_sfr` resolves to a real RegisterIR field; every `board_connection.pad` resolves to a real pad; every MemoryIR `access:` principal exists in the AOP principal set | point `mux_sfr` at `cosmos_nfc.no_such_reg` |
| `check-hw-ir-no-duplicate-literals.shs` | no hand-written literal in `src/**`/`examples/**` duplicates an address already owned by RegisterIR/MemoryIR (this is the §1.3 ratchet; **baselined at the current 14 occurrences of `0x43C00000`** and monotonically decreasing) | add an 8th hand-written `0x43C00000`; also fails if the baseline is stale (count dropped without the baseline being updated) |
| `check-hw-ir-generator-deterministic.shs` | generate twice into two trees, byte-identical; no timestamp, host path, or absolute path in any output | make a generator emit `now()` or iterate an unsorted map |
| `check-hw-ir-adapter-roundtrip.shs` | SVD/RDL/IP-XACT import -> export -> import is a fixed point on the representable subset; a lossy export without `--allow-lossy-export` FAILs; with it, the dropped set is present in the provenance header | export a block with `on_write` to SVD and assert a bare run FAILs; assert the flagged run records the drop |
| `check-hw-ir-ate-pin-groups.shs` | generated ATE pin groups and timing-set inputs are well-formed and cover every pad with a `test_mode_owner`; **asserts no output or doc string claims pattern generation** (the §3.4 boundary, checked as text) | add the phrase "generates ATPG patterns" to a generated doc header |

`check-hw-ir-generated-current.shs` is the load-bearing one and must land **before** the first
generated file is committed (§3.2).

---

## 7. Honest staging

### 7.1 Buildable now, no compiler work

- The SDN schema for all five IRs, and an SDN reader in pure Simple (SDN reading exists in
  `src/lib/common/sdn`; *inferred* that it is sufficient — verify before committing to it).
- All **text-emitting** generators: C header, Simple accessors, VHDL/SV register-block text, XDC/SDC,
  board tables, BSDL skeletons, MMIO tables, docs, SSpec test content, ATE pin groups, MBIST config,
  linker fragments. These are `.sdn` in, text out — runnable via `bin/simple run` today.
- All seven gates in §6 as `.shs` scripts.
- The import/export adapters (parsing SVD XML / RDL text / IP-XACT XML is ordinary text work).
- **Migration of `cosmos_nfc_regs.h` (210 lines) and `cosmos_pcie_regs.h` (270 lines)** to generated
  output — the highest-value first slice, because it converts a measured 14-occurrence duplication
  into one source and proves the diff gate against real content.

### 7.2 Needs compiler work

| Item | Blocker | Cite |
|---|---|---|
| `@reg(block=, offset=, access=)` source attribute (§7.2) | no such attribute exists; needs parser + attribute resolution + lowering to `RegRead`/`RegWrite`/`RegModify`/`RegFence` ops | grep for a `reg` attribute in `src/compiler/10.parser` returns nothing |
| First-class `effect(RegRead)` / `effect(PinDrive)` AOP selectors (§7.3) | selector vocabulary must be extended; §7.3 explicitly stages this after an interim `attr(reg)` + `within`/`execution` phase | SimpleEMU §7.3 |
| RegisterIR/MemoryIR lowering to **HWIR nodes** rather than text | strict modules may not claim registers or memories | `src/compiler/50.mir/hwir/types.spl:528-529` |
| Generated RTL register bank through the strict path | strict MIR lowering rejects clocked functions | `src/compiler/50.mir/hwir/mir_to_hwir.spl:588` |

The last two are **workstream A's clocked/memory tier**, not G's. G ships text emitters and switches
to HWIR nodes when A lands; the schema does not change when it does.

### 7.3 Blocked on the bootstrap redeploy

All four tracked stage binaries (`bootstrap/stage1|stage2|stage3/simple`,
`stage3/x86_64-unknown-linux-gnu/simple`) currently SEGV on both `compile` and `native-build`
(`.claude/rules/vcs.md`, stage-binaries guard, measured 2026-08-18: *"FAIL — 12 invocation(s)
executed across 4 binary(ies), 8 crashed/failed"*). Consequently:

- Anything requiring a **self-hosted full-CLI binary** — including running the generators on the
  default tooling path rather than the seed — waits on the redeploy.
- The §7.2 compiler work cannot be *deployed* until the redeploy lands, though it can be written and
  interpreter-tested.
- **Not blocked:** §7.1. Generators and gates run through `bin/simple run` on the current binary.

### 7.4 Suggested first increment

1. `check-hw-ir-generated-current.shs` + `check-hw-ir-schema-valid.shs`, with selftests and sabotage
   fixtures, **before any generated file exists**.
2. RegisterIR schema only (not all five). One block: `cosmos_nfc`, transcribed from
   `cosmos_nfc_regs.h:24-35`.
3. Two generators: C header and typed Simple accessors. Prove the regenerated C header is
   byte-identical to the committed hand-written one — that is the strongest possible correctness
   evidence, and it is available today.
4. Then the duplicate-literal ratchet, baselined at 14 and decreasing.

Everything else (PinIR, MemoryIR, ProtocolIR, EffectIR, adapters) waits until step 3 has landed
green. Adding five IRs and eleven generators before one round-trip is proven is exactly the
over-engineering this repo's rules forbid.

---

## 8. Explicit non-goals

- **No framework.** One schema, one reader, N small emitters. No plugin registry, no
  user-extensible field kinds, no dynamic IR.
- **No ATPG pattern generation, ever** (§3.4).
- **No new `rt_*` symbols in C or Rust.** All of G is pure Simple `.spl` plus `.shs` gates; the C
  headers it emits are *output*, not implementation.
- **No inheritance** in the IR model — composition and traits (a `Generator` trait with one method
  per emitter); generics written `<>`.
- **No second source of truth.** Imported SVD/RDL/IP-XACT files are converted once and retired, not
  read at build time (§4).
