# Native unsigned integer/float ordering lacks unsigned-aware coercion

- status: open
- severity: high for high-bit unsigned values
- component: MIR numeric coercion, LLVM-lib and Cranelift cast lowering

Mixed unsigned integer/float ordering cannot safely reuse the signed f64 cast:
LLVM-lib and Cranelift currently convert integer operands as signed values.
Add unsigned provenance to those cast paths, then extend the shared MIR
ordering promotion and dual-backend matrix for U8/U16/U32/U64 boundary and
high-bit values. Mixed-kind equality is already type-strict and needs no cast.
