# GDB end-to-end session — OpenOCD :3333 over the GHDL debug stack

Extends the Stage-5 OpenOCD attach (`openocd_attach.md`) to a full GDB
session: `gdb-multiarch` (riscv:rv64) → OpenOCD gdb server `:3333` →
`remote_bitbang :9999` → GHDL sim (`tb_openocd_bitbang`: `jtag_tap` →
`riscv_dtm` → `dmi_bus` → `riscv_debug_module` → `sba_test_mem`).

## Run

```sh
cd src/lib/hardware/debug
sh run_gdb_e2e.shs            # workdir defaults to /tmp/ghdl-jtag-gdb
```

The harness builds the glue `.so` + GHDL units (same steps as
`openocd_attach.md` §1), starts sim + OpenOCD, drives `gdb_e2e.gdb` in
batch, delivers the interactive halt (SIGINT → RSP `0x03`), tears down,
and prints machine-checked PASS/FAIL verdicts. Exit 0 = all pass; exit 2
= BLOCKED (no riscv-capable gdb installed).

## What is native GDB RSP vs monitor passthrough

| Operation | Path | Result |
|---|---|---|
| attach / halt-on-attach | native (`target extended-remote`) | pc captured |
| GPR read (`info registers`) | native `g`/`p` → abstract reads | full x0..pc dump |
| GPR write (`set $x5=0x123`) | native `P` → abstract write | read-back 0x123 |
| mem read (`x/4xw 0x10`) | native `m` → SBA 32-bit reads | init pattern |
| mem write (`set {u32}0x28`) | native `M` → SBA 32-bit write | 0xfeedc0de round-trip |
| pc write (`set $pc=0x100`) | native `P` → abstract dpc write | read-back 0x100 |
| single step | **monitor** `step` (qRcmd) → dcsr.step + resume + re-halt | pc 0x100 → 0x104 (+4) |
| continue | native `vCont;c` | hart free-runs |
| halt | native Ctrl-C → RSP `0x03` → haltreq | stop reply, pc=0x42f8 |
| detach | native `D` | clean, E2E_DONE |

### Why native `stepi` is deferred to hart integration
GDB's riscv stepping is breakpoint-based software single-step
(`riscv-tdep` decodes the insn at pc, plants a breakpoint at next-pc,
and resumes). That requires a hart that actually fetches and executes
from memory; the tb `fake_hart` is a free-running-pc model, so the
planted breakpoint would never hit and `stepi` waits forever.
Secondary gap: GDB's insn probe issues 16-bit reads while this DM's SBA
advertises 32/64-bit only (OpenOCD: `sysbus=skipped (unsupported
size)`). Both dissolve once a real rv32/rv64 hart with executable
memory sits behind the DM; the dcsr.step DM path itself is proven above
via the gdb monitor channel. A scripted `continue & … interrupt` also
cannot work in `-batch` (the CLI event loop does not pump the async stop
reply between script lines), hence the harness-delivered SIGINT — the
same interactive Ctrl-C flow, and fully native on the wire.

## Verified transcript (2026-07-22; gdb-multiarch 15.1, OpenOCD 0.12.0, GHDL 4.1.0 mcode)

Verdict block from `run_gdb_e2e.shs`:

```
PASS gpr-write   (x5=0x123)
PASS mem-rw-sba  (mem[0x28]=0xfeedc0de)
PASS mem-read-sba (init pattern @0x10)
PASS pc-write    (dpc abstract write, pc=0x100)
PASS step        (dcsr.step via gdb monitor channel: pc 0x100 -> 0x104, +4)
PASS cont-halt   (native continue/interrupt, re-halted at pc=0x42f8)
PASS session     (clean detach)
GDB_E2E: ALL PASS
```

Full gdb transcript (abridged only in the x1..x31 zero rows):

```
The target architecture is set to "riscv:rv64".
warning: No executable has been specified and target does not support
determining executable automatically.  Try using the "file" command.
0x0000000080003950 in ?? ()

=== attach state ===
PC_ATTACH=0x80003950

=== info registers (abstract GPR reads) ===
ra             0x0	0x0
sp             0x0	0x0
gp             0x0	0x0
tp             0x0	0x0
t0             0x0	0
  ... (2 zero GPR rows elided) ...
fp             0x0	0x0
  ... (23 zero GPR rows elided) ...
pc             0x80003950	0x80003950

=== GPR write: set $x5 = 0x123 ===
X5_BEFORE=0x0
X5_AFTER=0x123
t0             0x123	291

=== memory read via SBA: x/4xw 0x10 (sba_test_mem init pattern) ===
0x10:	0x00020002	0xa5a50000	0x00030003	0xa5a50000

=== memory write via SBA: 0xfeedc0de -> 0x28, read back ===
MEM28_AFTER=0xfeedc0de
0x28:	0xfeedc0de

=== pc write (abstract dpc write) + step via dcsr.step (expect pc+4) ===
PC_BEFORE=0x100
[riscv.cpu] Found 0 triggers
PC_AFTER=0x104

=== continue (native vCont;c) then halt (Ctrl-C -> RSP 0x03, from harness) ===
CONTINUE_STARTED

Program received signal SIGINT, Interrupt.
0x00000000000042f8 in ?? ()
PC_HALTED=0x42f8

=== detach ===
[Inferior 1 (Remote target) detached]
E2E_DONE
```

## Remaining hart-integration dependency
The hart behind the DM is still the tb model. Hart integration into the
real rv32/rv64 cores unblocks: native `stepi`/breakpoints (executing
hart + executable memory behind SBA or a progbuf), meaningful pc values,
and replacing the DM-resident stub CSRs (`debug_registers.vhd` header)
with the real CSR file. Until then this harness proves the complete
gdb↔OpenOCD↔DM protocol surface end-to-end.
