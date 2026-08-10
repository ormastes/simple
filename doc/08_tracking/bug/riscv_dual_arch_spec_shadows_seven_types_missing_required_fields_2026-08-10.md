# riscv_dual_arch_spec.spl shadows 7 kernel types — real fields/methods never exercised

- **File**: `test/unit/os/riscv_dual_arch_spec.spl` (whole file, 239 lines)
- **Real product code**: `src/os/kernel/arch/riscv_shared/dual_arch_contract.spl`,
  `src/os/kernel/arch/riscv_shared/backend_test_verify.spl`,
  `src/os/kernel/arch/riscv_shared/fpga_orchestration.spl`
- **Found during**: bounded first pass on `spec_shadow_reimplementation_worklist.tsv`

## What's wrong

The file declares 7 local classes (`ArchDescriptor`, `DualArchContract`,
`Rv32HardwareTree`, `QemuVirtContract`, `FpgaOrchestration`,
`BackendTestEntry`, `VerificationStage`, plus 3 more not in the worklist:
`LaneStatus`, `AcceptanceMatrix`, `PromotionGate`) that share names with real
kernel types but are NOT structurally compatible with them:

- Real `ArchDescriptor` has 9 fields (`has_m_ext`, `has_a_ext` in addition to
  the spec's 7) plus business-logic methods `is_rv32()`, `is_rv64()`,
  `is_gc()`, `linux_capable()`, and static factories `rv32gc()`/`rv64gc()` —
  none of which the spec exercises.
- Real `DualArchContract` has 9 fields (`rv32_isa/abi/mmu`, `rv64_isa/abi/mmu`
  in addition to the spec's 3) plus `both_linux_capable()`/
  `any_linux_capable()`/`is_symmetric()` and static factories
  `gc_contract()`/`rv64_only()` — the spec constructs a 3-field version
  directly and hand-computes the "both"/"any" logic inline instead of calling
  the real methods.
- Real `Rv32HardwareTree` and `QemuVirtContract` similarly have extra
  required fields (`boot_rom_addr/size`; `dtb_path`, `append_args`,
  `device_count`) and real business methods (`is_linux_minimal()`,
  `has_console()`, `is_rv32()/is_rv64()/has_kernel()/has_dtb()`) that the
  spec reimplements inline as free functions instead of calling.

Additionally: this file has no `describe`/`it` blocks — it's a `print`-based
smoke script with its own `main()`. It is not clear it runs under
`bin/simple test` at all; it may be dead code entirely.

## Why not fixed in this pass

Fixing requires supplying the additional required constructor fields for all
7+ shadowed types, replacing the spec's hand-rolled boolean logic with calls
to the real methods (`is_gc()`, `linux_capable()`, `both_linux_capable()`,
etc.), and converting the file to the `describe`/`it` sspec format (or
confirming it's dead and should be deleted) — beyond a bounded import-swap
pass.

## Unblock condition

Rewrite against the real `dual_arch_contract.spl` / `backend_test_verify.spl`
/ `fpga_orchestration.spl` types, filling all required fields, calling the
real business-logic methods (not reimplementing them), and converting to
`describe`/`it` so it participates in the daemon-run corpus and CI verdict.
