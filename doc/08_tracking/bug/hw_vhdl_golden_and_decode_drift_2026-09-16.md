# Hardware VHDL generator drift: golden mismatch, DDR window width, rv32 trap CSRs (2026-09-16)

Three independent lib-vs-spec disagreements in the VHDL generation lane, none
safely fixable spec-side without knowing which side is canonical:

## 1. exec_core_gen golden mismatch
- Spec: `test/01_unit/lib/hardware/vhdl_gen/exec_core_gen_spec.spl`
- Observed: `emits rv32_exec_core byte-identical to the golden` and
  `emits rv32_exec_core_flat byte-identical to the golden` fail
  (`assert_true failed: got false`); the rv64 variants pass.
- Expectation: generator output must match the checked-in golden, or the golden
  must be regenerated after a reviewed generator change.
- Unblock: diff generator output vs golden, decide which changed intentionally.

## 2. soc_vhdl_gen_rv64 DDR window decode width
- Spec: `test/01_unit/lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.spl`
  (1 remaining failure after stale-entity fixes landed today).
- Observed: spec expects `m_adr(31 downto 27) = "10000"` (128 MiB window);
  `src/lib/hardware/fpga_linux/_SocVhdlGen/peripherals.spl:685` emits
  `m_adr(31 downto 28) = "1000"` (256 MiB, matching its own
  0x80000000-0x8fffffff docstring).
- Expectation: exactly one of spec title ("canonical 128 MiB") and lib decode
  is right; the other must change.
- Unblock: hardware owner states the canonical window; then fix lib or spec.

## 3. rv32 trap completeness: CSR names MISSING
- Spec: `test/01_unit/lib/hardware/vhdl_gen/rv32_trap_completeness_spec.spl`
- Observed: `expected csr_mcause MISSING to equal csr_mcause present` (same for
  csr_mepc); 2 examples fail.
- Expectation: trap VHDL must expose mcause/mepc CSRs per the spec.
- Unblock: implement CSR exposure in the generator or revise the completeness
  contract deliberately.
