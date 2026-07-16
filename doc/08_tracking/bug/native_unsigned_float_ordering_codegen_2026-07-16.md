# Native unsigned integer/float ordering lacks unsigned-aware coercion

- status: source fixed 2026-07-16; dual-backend execution pending
- severity: high for high-bit unsigned values
- component: MIR numeric coercion, LLVM-lib and Cranelift cast lowering

Mixed unsigned integer/float ordering could not safely reuse the signed f64
cast because LLVM-lib and Cranelift converted integer operands as signed.

Shared MIR promotion now includes unsigned operands. LLVM text emits `uitofp`,
LLVM-lib carries unsigned local provenance to `LLVMBuildUIToFP`, and Cranelift
selects its existing unsigned conversion. The strict-dual case covers high-bit
U8/U16/U32/U64 values and the exact 2^63 boundary in both operand orders.
Mixed-kind equality remains type-strict and needs no cast. Executable evidence
awaits a runnable pure-Simple CLI.
