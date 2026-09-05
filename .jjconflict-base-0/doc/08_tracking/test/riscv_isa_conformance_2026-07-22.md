# RISC-V ISA Conformance — Directed Probe Suite Status (2026-07-22)

Lane R deliverable. Directed ISA-conformance net for the landed `.spl` core
models, driven directly at the documented core interfaces (no core changes):

- **rv64**: `std.hardware.rv64gc_rtl.core` — `core64_init` +
  `core64_combinational` + `core64_update`, with a 256-byte little-endian
  data memory attached to the `dmem_*` port (same wiring as
  `test/01_unit/lib/hardware/rv64gc_rtl/core64_probe.spl`).
- **rv32**: `std.hardware.rv32i_rtl.core` — `core_reset` +
  `core_combinational` + `core_update` with an **external** register file
  (write-back mirrors `soc_rtl/soc_top.spl` step 9).

## How to run

```bash
sh scripts/fpga/difftest_isa.shs                      # directed suite
sh scripts/fpga/difftest_isa.shs <elf_a> <elf_b> rv64 # + QEMU lockstep stage
# individual probes:
bin/simple run test/01_unit/lib/hardware/isa_conformance/rv64_isa_conformance_probe.spl
bin/simple run test/01_unit/lib/hardware/isa_conformance/rv32_isa_conformance_probe.spl
```

Output protocol per case: `PASS/FAIL/XFAIL/XPASS [class] name`, plus
`BLOCKED [class] reason` for cases that cannot execute at all. `FAIL` and
probe crashes gate red; `XFAIL` is an annotated known gap; `XPASS` is an
expected-fail that passed (inspect before trusting); `BLOCKED` is fail-closed
reporting, never green.

## Reference mechanism

The official riscv-tests are **not vendored** in this repo. This suite
synthesizes equivalent directed tests: hand-encoded R/I/S/B/U/J instructions
with architecturally-computed expected results (riscv-tests style: one
assertion per case, poison registers for control-flow checks).

`scripts/fpga/difftest_lockstep.shs` (dual-QEMU + gdb-multiarch per-`stepi`
PC/register compare of a Simple-compiled ELF vs a GCC ELF) exists as a
working-copy script but is **not in the committed tree**; `difftest_isa.shs`
Stage 2 reuses it when present and otherwise reports
`LOCKSTEP: BLOCKED (<exact reason>)` — it never silently greens.

## Results (2026-07-22, suite run green: rc=0, 0 hard failures)

### rv64 (`rv64_isa_conformance_probe.spl`) — 86 cases

| Class       | pass | fail | xfail | xpass | notes |
|-------------|-----:|-----:|------:|------:|-------|
| arith_imm   | 14   | 0    | 0     | 0     | addi/slti/sltiu/xori/ori/andi/slli/srli/srai/lui/auipc/addiw incl. RV64 sign-extension edges |
| arith_reg   | 15   | 0    | 0     | 0     | add/sub/sll/slt/sltu/xor/srl/sra/or/and + addw/subw/sllw/sraw incl. shamt masking (&63, &31) and 32-bit wrap |
| branch_jump | 12   | 0    | 0     | 0     | all six branches taken (poison-reg proof), not-taken fall-through, jal/jalr link values, final parked pc |
| load_store  | 10   | 0    | 0     | 0     | sd/ld, sw/lw/lwu, sh/lh/lhu, sb/lb/lbu, odd-address byte, store-width isolation |
| muldiv      | 0    | 0    | 11    | 1     | **XFAIL — M extension not wired** (see below) |
| amo         | 14   | 0    | 0     | 0     | amoadd/swap/xor/or/and/min/maxu (.d), amoadd.w sign-extension, lr/sc success + both invalidation paths |
| csr         | 7    | 0    | 0     | 0     | csrrw/csrrs/csrrc/csrrwi/csrrsi round-trips on mscratch, mhartid read |
| traps_rvc   | 0    | 0    | 2     | 0     | **XFAIL — misaligned trap + RVC** (see below) |
| csr_trap    | —    | —    | —     | —     | **BLOCKED — trap entry crashes the model** (see below) |

Totals: **pass=72 fail=0 xfail=13 xpass=1 blocked=1**.

### rv32 (`rv32_isa_conformance_probe.spl`) — 18 cases

| Class       | pass | fail | notes |
|-------------|-----:|-----:|-------|
| arith_imm   | 7    | 0    | addi/slti/sltiu/xori/srai/lui |
| arith_reg   | 3    | 0    | add (wrap), sub, sltu |
| branch_jump | 3    | 0    | beq/bltu taken (poison), jal link |
| load_store  | 4    | 0    | sw/lw, sb/lbu, sh/lhu, lb sign-extension |
| system      | 1    | 0    | ecall halts (documented rv32i model behavior — no trap file at this interface) |

Totals: **pass=18 fail=0**. M/A/CSR classes are **N/A** at the bare
`rv32i_rtl` core interface (RV32I only; CSR/trap logic lives in
`soc_rtl/soc_top.spl`) — covered on the rv64 core instead.

## XFAIL / BLOCKED rationale (honest annotations)

1. **muldiv (11 XFAIL + 1 XPASS, rv64).** The M extension is decoded
   (`decode.spl:221` sets `is_muldiv`) but `select_alu_op_64` routes
   `funct7==0x01` to an `ALU_ADD` **placeholder** ("M extension is handled
   separately") and `mul_div64_step` / `is_muldiv` have **no consumer** in
   `core64_combinational`, `core64_update`, or `soc_top_64_tick`. Every
   MUL/DIV/REM(-W) op computes `rs1+rs2`. The lone XPASS
   (`rem by zero == dividend`) is **coincidental**: the ADD placeholder gives
   `7+0=7`, which equals the architectural rem-by-zero result — it is not
   evidence of M support. Cross-lane fix: wire `mul_div64_step` into the
   rd_data mux (rv64gc_rtl owner). Note the *generated VHDL* rv32 PL core has
   a real divider (fixed in a9a344e96a3); this gap is specific to the `.spl`
   rv64 core model.
2. **traps_rvc: misaligned load (1 XFAIL, rv64).** `core64_combinational`
   has no alignment check on `dmem_addr`; a misaligned `lw` returns data
   instead of raising `CAUSE_MISALIGNED_LOAD` via mtvec. (Even if the check
   existed, trap *entry* was blocked at lane base; fixed on tip — see item 4.)
3. **traps_rvc: compressed/RVC (1 XFAIL, rv64).** 16-bit parcel reassembly
   (`pipeline_phase`/`fetch_low`) lives in the SoC fetch path, not in the
   direct `core64_combinational` interface; a raw `c.addi` word decodes as an
   unknown-opcode NOP there. RVC conformance must be tested through the SoC
   tick (rv32 PL-core precedent: `c.add` mis-decode fixed in a9a344e96a3).
4. **csr_trap (was BLOCKED at lane base, now PASS on tip).** At base
   `ddb8ebc8090` any *taken* trap crashed the interpreted model
   (`semantic: class TrapEnterResult64 has no field named csr_s`;
   `core64_update` read `trap.csr_s` but `TrapEnterResult64` lacked the
   field). Independently found by this suite; the fix landed in
   `3b36b68cd11` (Lane M S-mode work added `csr_s` to `TrapEnterResult64`).
   The mtvec-redirect / mepc==ecall-pc / mcause==11 cases are now real
   assertions in the probe and PASS on the current tip.
5. **Lockstep stage.** `difftest_lockstep.shs` is not in the committed tree
   (working-copy only). Stage 2 of `difftest_isa.shs` reports BLOCKED with
   the exact missing prerequisite whenever it cannot genuinely run.

## Cross-lane requests

- **rv64gc_rtl owner (Lane M):** (a) ~~fix `TrapEnterResult64.csr_s` crash~~
  DONE in `3b36b68cd11` (item 4); (b) wire the M unit (`mul_div64_step`)
  into the core datapath (item 1); (c) alignment-fault check or an explicit
  "no-misalign-trap" profile note (item 2).
- **Repo:** commit `scripts/fpga/difftest_lockstep.shs` so Stage 2 has a
  landed reference mechanism.
