# OpenOCD attach procedure — GHDL-simulated RISC-V debug stack (Stage 5)

Attach a real OpenOCD (verified with 0.12.0) to the simulated JTAG debug
stack — `jtag_tap` → `riscv_dtm` → `dmi_bus` → `riscv_debug_module`
(abstract GPR/CSR + SBA) → `sba_test_mem` — over the `remote_bitbang`
adapter protocol, served from the simulation by `tb_openocd_bitbang.vhd`
via the C socket glue `openocd_bitbang_glue.c` (VHPIDIRECT).

## Prerequisites
- `ghdl` (mcode backend is fine; that is what Ubuntu's `ghdl` package ships)
- `openocd` >= 0.11 with the `remote_bitbang` driver (stock Ubuntu build)
- a C compiler

## 1. Build

```sh
cd src/lib/hardware/debug
W=/tmp/ghdl-jtag && mkdir -p $W
cc -shared -fPIC -o $W/bb_glue.so openocd_bitbang_glue.c
ghdl -a --std=08 --workdir=$W \
    jtag_tap.vhd riscv_dtm.vhd dmi_bus.vhd debug_registers.vhd \
    riscv_debug_module.vhd sba_test_mem.vhd tb_openocd_bitbang.vhd
```

Note (mcode backend): the foreign subprograms are declared as
`"VHPIDIRECT bb_glue.so <symbol>"`, so the shared library is resolved by
dlopen at elaboration — `bb_glue.so` must be findable via
`LD_LIBRARY_PATH`. With a gcc/llvm GHDL backend you may instead link an
object file with `ghdl -e -Wl,...` and drop the lib name from the strings.

## 2. Start the simulation (terminal 1)

```sh
cd $W && LD_LIBRARY_PATH=$W ghdl -r --std=08 --workdir=$W tb_openocd_bitbang
# [bitbang] listening on 127.0.0.1:9999, waiting for OpenOCD
```

The sim blocks until OpenOCD connects, then executes one bitbang protocol
byte per 5 ns of simulated time. It finishes when OpenOCD disconnects.

## 3. Attach OpenOCD (terminal 2)

```sh
cd src/lib/hardware/debug
openocd -f openocd_riscv_sim.cfg \
  -c 'init' -c 'targets' \
  -c 'halt' -c 'reg pc' \
  -c 'mdd 0x10 2' \
  -c 'mww phys 0x28 0xfeedc0de' -c 'mdw phys 0x28' \
  -c 'step' -c 'reg pc' \
  -c 'resume' -c 'shutdown'
```

Memory access uses the System Bus (`riscv set_mem_access sysbus` in the
cfg) — SBA is the only memory path (progbufsize=0).

## Verified transcript (2026-07-22, OpenOCD 0.12.0, GHDL 4.1.0 mcode)

```
Info : JTAG tap: riscv.cpu tap/device found: 0x15350067 (mfg: 0x033 (IDT), part: 0x5350, ver: 0x1)
Info : datacount=2 progbufsize=0
Info : Examined RISC-V core; found 1 harts
Info :  hart 0: XLEN=64, misa=0x8000000000001101
 0* riscv.cpu          riscv      little riscv.cpu          running
pc (/64): 0x0000000080002e0c
0x00000010: a5a5000000020002 a5a5000000030003
0x00000028: feedc0de
Info : [riscv.cpu] Found 0 triggers
pc (/64): 0x0000000080002e10
shutdown command invoked
```

Evidence read-out: examine completes (XLEN=64 discovered via abstract GPR
reads, misa from the DM stub CSR); `halt` captures pc into dpc; `mdd`
returns the `sba_test_mem` init pattern words 2 and 3 through real 64-bit
SBA reads; `mww`/`mdw` round-trip a 32-bit SBA write; `step` advances pc
by exactly one instruction (dcsr.step + resumereq + re-halt); `resume` and
`shutdown` are clean (exit code 0).

## Stub honesty — what is NOT real yet

The hart behind the DM is still the testbench model (`fake_hart` +
`gpr_model` in `tb_openocd_bitbang.vhd`); hart integration into
rv32/rv64 cores is the deferred plan item. To let the riscv-013 driver
run without a program buffer, `debug_registers.vhd` carries DM-resident
stub CSRs (documented in its header): misa (RO constant RV64IMA),
mstatus (RW scratch), tselect/tdata1 (0 triggers). These are replaced by
the real hart CSR file at hart integration. GDB was not exercised in this
pass (OpenOCD's gdb server does listen on :3333; `gdb -ex 'target
extended-remote :3333'` is the follow-up once a real hart is attached —
against the stub hart a GDB session would only re-prove the same DM paths).
