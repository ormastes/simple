# Isel Riscv64 scenario manual

Executable source: test/01_unit/compiler/backend/native/isel_riscv64_spec.spl.

| Scenarios | Active | Skipped |
|---|---|---|
| 42 | 42 | 0 |

Requirement: REQ-COMPILER-BACKEND-001, as annotated in source.

## Scenarios

- uses the shared LP64D contract word size
- keeps RV64 Linux ABI metadata explicit
- emits RV64 prologue saves for ra and s0
- materializes large RV64 prologue frame offsets
- materializes large RV64 epilogue frame offsets
- uses 64-bit load and store opcodes for RV64 memory
- uses RV64 word-size offsets for field access
- materializes RV64 out-of-range field offsets
- moves RV64 return values into a0 before RET
- emits RV64 epilogue restores for ra and s0
- selects RV64 arithmetic opcodes for MIR binary ops
- selects RV64 comparison opcodes for MIR binary ops
- selects RV64 bitwise, shift, div, and rem opcodes
- selects RV64 MV for MIR copy and move instructions
- materializes RV64 string constants as data references
- materializes RV64 zero constants as LI zero
- preserves RV64 large integer constants
- selects RV64 JAL for MIR goto terminators
- selects RV64 branch and jump opcodes for MIR if terminators
- selects RV64 compare and default jump opcodes for MIR switch terminators
- selects RV64 NOP for MIR unreachable terminators
- traps on RV64 Abort without fallthrough
- selects RV64 unary opcodes
- uses RV64 word-size stack slots for call arguments after a7
- materializes RV64 out-of-range stack argument offsets
- does not move a return register for RV64 void calls
- fails closed with RV64 NOP for unsupported call targets
- selects RV64 JALR for MIR indirect calls
- selects RV64 JALR for MIR CallIndirect instructions
- selects RV64 stack allocation and cast opcodes
- materializes RV64 large stack allocation sizes
- selects RV64 NOP for MIR nop instructions
- fails closed with RV64 NOP for unsupported MIR instructions
- fails closed with RV64 NOP for unsupported arithmetic ops
- fails closed with RV64 NOP for unsupported MIR constants
- selects RV64 address arithmetic for MIR get-element-pointer
- selects RV64 JALR for MIR CallIndirect instructions
- selects rotates and unary bitmanip helpers
- keeps unsupported or malformed intrinsics inert
- lowers rotate intrinsics through the RV64 module path
- lowers clz/ctz/bswap intrinsics through the RV64 module path
- fails closed with RV64 NOP for unsupported MIR intrinsics

## Reproduction

```text
<runtime> test test/01_unit/compiler/backend/native/isel_riscv64_spec.spl --mode=interpreter
```

## Evidence and limits

Restored missing helper bodies from pre-transplant f2378f0b4c8 into test/fixtures/compiler/native/rv64_isel_builders.spl and rv64_isel_control_fixtures.spl. Existing assertions remain; Abort now asserts exactly one EBREAK with zero NOP instructions, matching production divergence.
Focused current-owner Stage 1 diagnostics passed 35 of 36 previously failing scenarios; the stale Abort oracle was corrected and passed separately. The six baseline green scenarios were not replayed after repair.
Source-inline diagnostics use actual release owner text and historical fixtures with cached bootstrap support. They do not prove admitted self-hosted import closure or native execution. Required compiler/core/MCP/LSP gates remain outstanding.
Evidence: build/phase1-backend-fixtures-20261011.