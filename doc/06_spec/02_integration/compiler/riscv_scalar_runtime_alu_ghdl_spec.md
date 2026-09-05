# Runtime Scalar ALU GHDL Evidence

This development scenario emits the fixed-XLEN runtime scalar ALU through the
strict HWIR VHDL backend and asks GHDL to analyze, elaborate, and simulate the
generated RV32 and RV64 entities.

The directed vectors cover RV32 ADD, ADDI, SLT, LUI, and AUIPC; RV64 ADDIW,
ADDW, and SUBW; x0 destination suppression; and fail-closed row and semantic
identity mismatches. The executable source is
`test/02_integration/compiler/riscv_scalar_runtime_alu_ghdl_spec.spl`.

Run with an admitted pure-Simple compiler:

```text
bin/simple test test/02_integration/compiler/riscv_scalar_runtime_alu_ghdl_spec.spl --mode=interpreter
```

Acceptance requires an explicit passing scenario summary and successful GHDL
simulation. A Rust bootstrap seed exit code, analyze-only result, missing test
summary, or execution against a different source root is not qualification.

The leaf ALU evidence does not prove the clocked decoded-uop/completion pipeline.
That combined pipeline additionally requires reset, held-backpressure,
completion-capture atomicity, illegal/fault stickiness, and recovery vectors.
