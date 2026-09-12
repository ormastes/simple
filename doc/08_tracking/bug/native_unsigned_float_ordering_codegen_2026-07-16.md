# Native unsigned integer/float ordering lacks unsigned-aware coercion

**Status:** CLOSED-STALE (2026-09-12: source fix recorded but staged platform execution never completed; not re-verifiable from the record)

- status: source fixed -> CLOSED-STALE 2026-09-12; staged dual-backend platform execution pending
- severity: high for high-bit unsigned values
- component: MIR numeric coercion, LLVM-lib and Cranelift cast lowering

Mixed unsigned integer/float ordering could not safely reuse the signed f64
cast because LLVM-lib and Cranelift converted integer operands as signed.

Shared MIR promotion now includes unsigned operands. LLVM text emits `uitofp`,
LLVM-lib carries unsigned local provenance to `LLVMBuildUIToFP`, and Cranelift
selects its existing unsigned conversion. The strict-dual case covers high-bit
U8/U16/U32/U64 values and the exact 2^63 boundary in both operand orders.
Mixed-kind equality remains type-strict and needs no cast. Linux runs this case
in the full gate; macOS arm64/x64 and Windows x64 select it explicitly. The
cross-module Result fixture carries high-bit controls through both backends on
AArch64/RISC-V QEMU and FreeBSD. First staged matrix execution is pending.

## Triage 2026-09-12
Older than 45 days with the described staged-platform execution still pending; closing per age policy. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
