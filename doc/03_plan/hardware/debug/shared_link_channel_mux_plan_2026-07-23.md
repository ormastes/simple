# Shared-Link Channel Mux + FPGA JTAG Routing — Plan (2026-07-23)

## Goal (mission, not just the infra)

Stand up a **configurable multi-channel debug link** so ONE physical wire carries
**log + terminal-IO + JTAG** at once, with an **FPGA-side mux/demux** and a
**host-side demux/mux + JTAG-interface emulator**. Then USE it to:

1. **Debug Linux booting** on the Simple RISC-V SoC (serial console + JTAG halt/
   step/memory on the same link).
2. Run a **1-minute** and a **10-minute hard job** to exercise RV32/RV64
   robustness under load.
3. **Fix any bug** the robustness runs surface (root-cause in `.spl`, not the
   Rust seed; regression test each fix).

The mux/JTAG infra is the *enabler*; boot-debug + the 1/10-min robustness loop +
bug fixes are the deliverable.

## Why one link

The K26/KV260 PL brings a single UART pair to physical pins (`uart_tx→H12`,
`uart_rx→E10`, PMOD J2 — `scripts/fpga/k26_rv64.xdc:4-7`); the carrier USB-UARTs
are PS-side. On-chip debug currently rides the Zynq PS/BSCAN native JTAG, not PL
pins. To get **serial + JTAG + log to the host over that one PL link** we
multiplex. This does **not** remove the pending PMOD-3v3-adapter gap (H12/E10 is
still PL-side) — it makes all three channels share the one link *once the adapter
is present*. Sim (GHDL) validation does not need the adapter.

## Research anchors (verified `file:line`)

- **JTAG tunnel points.** Raw pins on the TAP: `jtag_tap.vhd:30-54`
  (`tck/tms/tdi/trst_n` in, `tdo` out). Higher-level DMI transaction bus (the
  efficient tunnel): `riscv_dtm.vhd:44-51` — `dmi_valid, dmi_addr[6:0],
  dmi_wdata[31:0], dmi_op[1:0]` out / `dmi_rdata[31:0], dmi_resp[1:0], dmi_ready`
  in (same shape in `dmi_bus.vhd:26-50`, `hart_core_glue.vhd:43-49`).
- **remote_bitbang protocol** (`tb_openocd_bitbang.vhd:266-285`): bytes `'0'..'7'`
  = `{tck,tms,tdi}` packed `v=tck*4+tms*2+tdi`; `'R'` = sample TDO and reply
  `'0'/'1'`; `'r/s/t/u'` = trst; `'Q'` = quit. Host glue `openocd_bitbang_glue.c`
  is a VHPIDIRECT byte-pipe (`bb_init`/`bb_next`/`bb_send`).
- **UART model.** SoC level `soc_top_64.spl:96-100` (`uart_tx:[i64]` TX log,
  `uart_rx:[i64]` RX queue, `uart_ier`); THR append `:311-312`; RX inject
  `soc64_uart_push_rx :321-326`; LSR `:197,224-225`. Device model
  `uart16550.spl` (RBR/THR/LSR, 16-deep FIFOs).
- **FPGA top is TX-only** — `soc_top_rv32.vhd:7-14` (`uart_tx:out std_logic`,
  **no RX, no PL JTAG pins**). Mux TX inserts at `soc_top_rv32.vhd:61`
  (`uart_tx <= uart_tx_core`); **the RX/demux path is net-new RTL.**
- **No SLIP/COBS/HDLC exists** in `src/lib/` — framer is net-new. Reuse
  `Crc32`/`Adler32` (`src/lib/common/bytes/checksum.spl:28,62`).
- **Config model to mirror**: `RiscvPlatform` (`platform.spl:24`), `XlenConfig`
  (`xlen.spl:23`), `K26XdcConfig` (`fpga_k26/k26_xdc.spl:19`) — plain structs +
  named factories.
- **Host tool MUST be `.spl`** (CLAUDE.md: all code `.spl`/`.shs`; pure-Simple
  first). Serial/socket in the `nogc_sync_mut` tier; a thin C/SFFI termios shim
  only if no Simple `/dev/tty*` wrapper exists.

## Design

### Frame format — ONE committed format (no framing plugin)

`COBS( channel_byte ++ payload ) ++ 0x00`, with a `CRC16` over
`channel_byte ++ payload` carried as the last 2 payload bytes.

- **COBS** delimiting: `0x00` is the frame terminator; COBS removes all `0x00`
  from the body (bounded ≤1 overhead byte per 254). Clean resync: after any
  garbage, the next `0x00` starts a fresh frame. Chosen over SLIP (no
  delimiter-in-payload doubling) and length-prefix (self-syncing).
- **channel_byte**: 0=`LOG`, 1=`TERM`, 2=`JTAG`, 3=`CTRL` (reset/baud/probe).
  Channel count/assignment is config, not hardcoded semantics.
- **CRC16** (CCITT) over channel+payload; a bad CRC drops the frame (no ACK on
  the sim link; CTRL-channel ret/seq is a Phase-2 concern if needed).

*Configurability* is the **transport profile** (below), NOT swapping the frame
format. One format, documented, fuzzed.

### TransportProfile (mirrors `RiscvPlatform`)

```
struct TransportProfile:
    name: text                 # "k26-pmod-uart", "arty-uart", "sim-loopback"
    jtag_mode: JtagMode        # BITBANG (Phase 1) | DMI_TUNNEL (Phase 2)
    baud: i64                  # 115200 default
    max_frame: i64             # COBS body cap
    chan_log: i64  chan_term: i64  chan_jtag: i64  chan_ctrl: i64
    crc: bool                  # on by default
# factories: transport_sim_loopback(), transport_k26_pmod(), transport_arty()
```

### FPGA side (RTL, generated from `.spl` model, soc_rtl style)

- **TX mux**: arbitrate {LOG bytes from `uart_tx`, TERM TX, JTAG responses} into
  framed bytes on the single physical `uart_tx`. Round-robin with per-channel
  FIFOs; **fairness = no channel starves** (a bulk log burst must not block a
  JTAG reply). Small credit/quantum scheduler.
- **RX demux**: parse framed bytes from the (net-new) physical `uart_rx`, verify
  CRC, route by channel: TERM→core RBR (`soc64_uart_push_rx`), JTAG→tap, CTRL→
  reset/probe.
- **JTAG in-path** (configurable):
  - **Phase 1 BITBANG**: demux JTAG channel bytes = remote_bitbang commands, drive
    `jtag_tap` `tck/tms/tdi`, sample `tdo`, frame the reply. Reuses the *proven*
    tb_openocd_bitbang semantics end-to-end.
  - **Phase 2 DMI_TUNNEL**: JTAG channel carries DMI transactions
    `{addr7,wdata32,op2}`→`{rdata32,resp2}`, driving `dmi_bus` directly (bypasses
    `jtag_tap`/`dtm`). Fewer bytes/txn; needs host DTM emulation.

### Host side (`.spl`, `nogc_sync_mut`)

- Open the shared serial (Simple `net`/`fs` wrapper; thin termios SFFI only if
  needed). Demux frames → **LOG** to file/stdout, **TERM** to a PTY (so a normal
  terminal attaches), **JTAG** to the JTAG bridge.
- **JTAG bridge**:
  - **Phase 1**: listen as `remote_bitbang` on `127.0.0.1:9999` (stock OpenOCD,
    `openocd_riscv_sim.cfg`); pipe bitbang bytes ↔ JTAG channel frames. Near-dumb.
  - **Phase 2**: host **TAP/DTM emulator** — turn OpenOCD's bitbang wiggles into
    DMI transactions (faithful DTMCS/dmireset, DMI busy/retry sticky, IR/DR
    shift). Hardest component; build only when measured necessary.

### Bandwidth math (why Phase-2 is *measured*, not assumed)

Raw bitbang: one DMI read/write ≈ (IR-shift + 41-bit DR-shift)×~3 bitbang bytes/
bit ≈ **~150-200 link bytes each way**. At 115200 baud (~11.5 KB/s) ⇒ **~50-70
DMI txn/s**. DMI-tunnel frame ≈ channel+addr+data+crc+COBS ≈ **~10 bytes** ⇒
**~1000 txn/s**. Phase-2 trigger = *Phase-1 throughput measurably lengthens the
1/10-min job or makes step-debug painful* — a number from the robustness runs,
not a vibe.

## Phases (each lands independently; Phase 1 first)

| # | Deliverable | Test gate |
|---|---|---|
| **1** | Framing lib (`src/lib/hardware/link_mux/frame.spl`: COBS+CRC16+channel) | property/fuzz specs (below) — pure `.spl`, no HW |
| **2** | Host tool (`src/app/link_mux/`): serial open, demux→log/PTY, remote_bitbang bridge (BITBANG) | host specs: bitbang↔frame pipe, PTY echo, log split |
| **3** | FPGA RTL mux/demux + **RX path** (`src/lib/hardware/link_mux/*_rtl.spl` → VHDL) | `tb_channel_mux.vhd` GHDL: TX frame-out, RX demux-route, fairness |
| **4** | **E2E gate**: OpenOCD→host→framed UART→FPGA demux→DTM (IDCODE/DMSTATUS) | new gate in `check-riscv-hardware-gates.shs` |
| **5** | **Boot-debug + robustness loop**: attach console+JTAG during Linux boot; 1-min & 10-min hard jobs; fix bugs | boot reaches `/init` under mux; hard jobs green; each bug → regression test |
| **6** (opt, measured) | DMI_TUNNEL + host DTM emulator | DMI-txn specs + reuse Phase-4 gate under `jtag_mode=DMI_TUNNEL` |

## Intensive tests (what catches real bugs, run in a loop)

- **Framing (Phase 1)**: property `decode(encode(chan,payload)) == (chan,payload)`
  over random channel/payload incl. `0x00`-heavy and max-size; **resync-from-
  garbage** (junk prefix → next valid frame recovered); **CRC single-bit-flip →
  frame rejected**; empty/1-byte/oversize edge frames.
- **Mux (Phase 3)**: **interleave fairness** — saturate LOG while JTAG replies;
  assert no JTAG starvation and no cross-channel byte leakage; RX partial-frame /
  split-across-reads reassembly.
- **E2E (Phase 4)**: OpenOCD reads IDCODE `0x15350067` + DMSTATUS through the mux;
  a memory read/write via SBA round-trips; wired into the aggregate gate.
- **Robustness (Phase 5)**: 1-min & 10-min hard jobs (below) on RV32 + RV64;
  each observed via the muxed console+JTAG; any hang/wrong-result → JTAG halt +
  register/memory dump → root-cause → `.spl` fix + regression probe.

### Candidate 1-min / 10-min hard jobs
- **1-min**: coremark-ish integer loop / memcpy+checksum sweep / the existing
  rv32 64 KB load-path checksum (`check_linux_loading_rv32.shs`) scaled up.
- **10-min**: Linux boot → userspace `/init` loop doing FS + integer + trap
  churn; or a long RV64 arithmetic/mmu-stress kernel under `soc_top_64` with
  difftest-style invariants.

## Board-runnable honesty

Validation this plan commits to: **GHDL-tb + sim green** for framing, mux, and
the E2E JTAG-over-mux path; **host tool tested** against the sim link. The
physical-board path (K26 PMOD H12/E10 + 3v3 adapter) is **documented and gated on
the adapter** — not claimed board-proven until captured with a serial/SSH/JTAG
transcript per `.claude/rules/board-runnable.md`. QEMU/GHDL is the harness; the
board is the target.

## Files (planned)
- `src/lib/hardware/link_mux/frame.spl` — COBS + CRC16 + channel framing (Phase 1)
- `src/lib/hardware/link_mux/transport_profile.spl` — `TransportProfile` config
- `test/01_unit/lib/hardware/link_mux/frame_spec.spl` — property/fuzz tests
- `src/app/link_mux/` — host demux/mux + remote_bitbang bridge (Phase 2)
- `src/lib/hardware/link_mux/mux_rtl.spl` + `tb_channel_mux.vhd` (Phase 3)
- gate wiring in `scripts/check/check-riscv-hardware-gates.shs` (Phase 4)
