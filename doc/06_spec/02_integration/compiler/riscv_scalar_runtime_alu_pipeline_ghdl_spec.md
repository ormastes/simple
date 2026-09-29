# Runtime Scalar ALU Pipeline GHDL Evidence

This development scenario emits and clocks the complete fixed-XLEN runtime ALU
pipeline: declarative decoder, decoded-uop skid, shared ALU, atomic acceptance
gate, completion skid, typed default effects, and sticky fault owner.

The RV32 flow captures ADD, holds its completion while downstream ready is low,
mutates live top-level inputs, verifies the registered payload remains stable,
and consumes the completion exactly once. It then checks that a legal non-ALU
row latches a protocol fault and recovers only after reset. An illegal encoding
instead produces one held cause-2 architectural completion with the original
instruction as `tval`, zero effects, and exact event identity. The RV64 flow
verifies ADDIW sign extension and one-time completion consumption.

Executable scenario:
`test/02_integration/compiler/riscv_scalar_runtime_alu_pipeline_ghdl_spec.spl`

Run only with an admitted pure-Simple compiler:

```text
bin/simple test test/02_integration/compiler/riscv_scalar_runtime_alu_pipeline_ghdl_spec.spl --mode=interpreter
```

Qualification requires a passing scenario summary, successful GHDL simulation,
the generated RTL SHA-256 and pipeline graph SHA-256, GHDL version/log, and the
compiler admission receipt. A bootstrap-seed exit status or failure before this
spec loads is not evidence.

The scenario requires GHDL and creates a unique work directory for each RV32
and RV64 simulation. Missing GHDL is a failure in this release-evidence lane;
the work library is never shared with concurrent simulations.
